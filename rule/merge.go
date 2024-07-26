/* Copyright 2018 The Bazel Authors. All rights reserved.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

package rule

import (
	"bytes"
	"encoding/hex"
	"errors"
	"fmt"
	"io"
	"log"
	"os"
	"reflect"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"unsafe"

	bzl "github.com/bazelbuild/buildtools/build"
)

var ShouldLog = false

func init() {
	d, err := os.Getwd()
	if err != nil {
		log.Fatal(err)
	}
	if strings.Contains(d, "select") {
		ShouldLog = true
	}

	Config.MaxDepth = 1
}

func Debug(format string, args ...interface{}) {
	if ShouldLog {
		fmt.Printf(format+"\n", args...)
	}
}

func DebugCond(cond bool, msg string, args ...any) {
	if cond {
		Debug(msg, args...)
	}
}



// MergeRules copies information from src into dst, usually discarding
// information in dst when they have the same attributes.
//
// If dst is marked with a "# keep" comment, either above the rule or as
// a suffix, nothing will be changed.
//
// If src has an attribute that is not in dst, it will be copied into dst.
//
// If src and dst have the same attribute and the attribute is mergeable and the
// attribute in dst is not marked with a "# keep" comment, values in the dst
// attribute not marked with a "# keep" comment will be dropped, and values from
// src will be copied in.
//
// If dst has an attribute not in src, and the attribute is mergeable and not
// marked with a "# keep" comment, values in the attribute not marked with
// a "# keep" comment will be dropped. If the attribute is empty afterward,
// it will be deleted.

// onlyInDst := key in dst && key not in src
// if onlyInDst && (isMergeable(key) && !ShouldKeep(dst[key])):
//   delete dst[key]

func MergeRules(src, dst *Rule, mergeable map[string]bool, filename string) {
	if dst.ShouldKeep() {
		return
	}

	// Process attributes that are in dst but not in src.
	// Debug("~~~Merging %s into %s", src.Name(), dst.Name())
	for key, dstAttr := range dst.attrs {
		if _, ok := src.attrs[key]; ok || !mergeable[key] || ShouldKeep(dstAttr.expr) {
			continue
		}
		// if attr not in src, and attr is mergeable, and attr is not marked with # keep
		// then delete the attr from dst
		
		if mergedValue, err := mergeAttrValues(nil, &dstAttr); err != nil {
			start, end := dstAttr.expr.RHS.Span()
			log.Printf("%s:%d.%d-%d.%d: could not merge expression wat", filename, start.Line, start.LineRune, end.Line, end.LineRune)
			log.Printf("%v", err)
		} else if mergedValue == nil {
			dst.DelAttr(key)
		} else {
			dst.SetAttr(key, mergedValue)
		}
	}

	// Merge attributes from src into dst.
	for key, srcAttr := range src.attrs {
		if dstAttr, ok := dst.attrs[key]; !ok {
			dst.SetAttr(key, srcAttr.expr.RHS)
		} else if mergeable[key] && !ShouldKeep(dstAttr.expr) {
			if mergedValue, err := mergeAttrValues(&srcAttr, &dstAttr); err != nil {
				start, end := dstAttr.expr.RHS.Span()
				log.Printf("%s:%d.%d-%d.%d: could not merge expression foo", filename, start.Line, start.LineRune, end.Line, end.LineRune)
			} else if mergedValue == nil {
				dst.DelAttr(key)
			} else {
				dst.SetAttr(key, mergedValue)
			}
		}
	}

	dst.private = src.private
}

// mergeAttrValues combines information from src and dst and returns a merged
// expression. dst may be modified during this process. The returned expression
// may be different from dst when a structural change is needed.
//
// The following kinds of expressions are recognized.
//
//   * nil
//   * strings (can only be merged with strings)
//   * lists of strings
//   * a call to select with a dict argument. The dict keys must be strings,
//     and the values must be lists of strings.
//   * a list of strings combined with a select call using +. The list must
//     be the left operand.
//   * an attr value that implements the Merger interface.
//
// An error is returned if the expressions can't be merged, for example
// because they are not in one of the above formats.
func mergeAttrValues(srcAttr, dstAttr *attrValue) (bzl.Expr, error) {
	if ShouldKeep(dstAttr.expr.RHS) {
		return nil, nil
	}
	var dstHasMerger bool
	var srcHasMerger bool
	var dstVal any
	var srcVal any
	if dstAttr != nil {
		_, dstHasMerger = dstAttr.val.(Merger)
		dstVal = dstAttr.val
	}
	if srcAttr != nil {
		_, srcHasMerger = srcAttr.val.(Merger)
		srcVal = srcAttr.val
	}
	Debug("src has merger: %v", srcHasMerger)
	Debug("dst has merger: %v", dstHasMerger)
	if !srcHasMerger && !dstHasMerger {
		Debug("src and dst do not have mergers")
		Debug("src: %v", Dump(srcVal))
		Debug("dst: %v", Dump(dstVal))
	}

	dst := dstAttr.expr.RHS
	if srcAttr == nil && (dst == nil || isScalar(dst)) {
		return nil, nil
	}
	if srcAttr != nil && isScalar(srcAttr.expr.RHS) {
		return srcAttr.expr.RHS, nil
	}

	if _, ok := dstAttr.val.(Merger); srcAttr == nil && ok {
		Debug("warning: src was nil but dst implements Merger. dropping dst")
		// val := dstAttr.val.(Merger).Merge(nil)
		// return val, nil
		return nil, nil
	}

	if srcAttr != nil {
		if srcMerger, ok := srcAttr.val.(Merger); ok {
			val := srcMerger.Merge(dst)
			Debug("src is a Merger %#v", srcAttr.val)
			Debug("Merged to %#v", val)
			return val, nil
		}
	}
	var srcExprs platformStringsExprs
	var err error
	if srcAttr != nil {
		srcExprs, err = extractPlatformStringsExprs(srcAttr.expr.RHS)
		if err != nil {
			return nil, err
		}
	}

	dstExprs, err := extractPlatformStringsExprs(dst)
	if err != nil {
		return nil, err
	}
	mergedExprs, err := mergePlatformStringsExprs(srcExprs, dstExprs)
	if err != nil {
		return nil, err
	}
	return makePlatformStringsExpr(mergedExprs), nil
}

func mergePlatformStringsExprs(src, dst platformStringsExprs) (platformStringsExprs, error) {
	var ps platformStringsExprs
	var err error
	ps.generic = MergeList(src.generic, dst.generic)
	if ps.os, err = MergeDict(src.os, dst.os); err != nil {
		return platformStringsExprs{}, err
	}
	if ps.arch, err = MergeDict(src.arch, dst.arch); err != nil {
		return platformStringsExprs{}, err
	}
	if ps.platform, err = MergeDict(src.platform, dst.platform); err != nil {
		return platformStringsExprs{}, err
	}
	return ps, nil
}

// MergeList merges two bzl.ListExpr of strings. The lists are merged in the
// following way:
//
//   - If a string appears in both lists, it appears in the result.
//   - If a string appears in only src list, it appears in the result.
//   - If a string appears in only dst list, it is dropped from the result.
//   - If a string appears in neither list, it is dropped from the result.
//
// The result is nil if both lists are nil or empty.
//
// If the result is non-nil, it will have ForceMultiLine set if either of the
// input lists has ForceMultiLine set or if any of the strings in the result
// have a "# keep" comment.
func MergeList(srcExpr, dstExpr bzl.Expr) *bzl.ListExpr {
	src, isSrcLis := srcExpr.(*bzl.ListExpr)
	dst, isDstLis := dstExpr.(*bzl.ListExpr)
	if !isSrcLis && !isDstLis {
		return nil
	}
	if dst == nil {
		return src
	}
	if src == nil {
		src = &bzl.ListExpr{List: []bzl.Expr{}}
	}

	// Build a list of strings from the src list and keep matching strings
	// in the dst list. This preserves comments. Also keep anything with
	// a "# keep" comment, whether or not it's in the src list.
	srcSet := make(map[string]bool)
	for _, v := range src.List {
		if s := stringValue(v); s != "" {
			srcSet[s] = true
		}
	}

	var merged []bzl.Expr
	kept := make(map[string]bool)
	keepComment := false
	for _, v := range dst.List {
		s := stringValue(v)
		if keep := ShouldKeep(v); keep || srcSet[s] {
			keepComment = keepComment || keep
			merged = append(merged, v)
			if s != "" {
				kept[s] = true
			}
		}
	}

	// Add anything in the src list that wasn't kept.
	for _, v := range src.List {
		if s := stringValue(v); kept[s] {
			continue
		}
		merged = append(merged, v)
	}

	if len(merged) == 0 {
		return nil
	}
	return &bzl.ListExpr{
		List:           merged,
		ForceMultiLine: src.ForceMultiLine || dst.ForceMultiLine || keepComment,
	}
}

// MergeDict merges two bzl.DictExpr, src and dst, where the keys are strings
// and the values are lists of strings.
//
// If both src and dst are non-nil, the keys in src are merged into dst. If both
// src and dst have the same key, the values are merged using MergeList.
// If the same key is present in both src and dst, and the values are not compatible,
// an error is returned.
func MergeDict(srcExpr, dstExpr bzl.Expr) (*bzl.DictExpr, error) {
	src, isSrcDict := srcExpr.(*bzl.DictExpr)
	dst, isDstDict := dstExpr.(*bzl.DictExpr)
	if !isSrcDict && !isDstDict {
		return nil, fmt.Errorf("expected dict, got %s and %s", srcExpr, dstExpr)
	}
	if dst == nil {
		return src, nil
	}
	if src == nil {
		src = &bzl.DictExpr{List: []*bzl.KeyValueExpr{}}
	}

	var entries []*dictEntry
	entryMap := make(map[string]*dictEntry)

	for _, kv := range dst.List {
		k, v, err := dictEntryKeyValue(kv)
		if err != nil {
			return nil, err
		}
		if _, ok := entryMap[k]; ok {
			return nil, fmt.Errorf("dst dict contains more than one case named %q", k)
		}
		e := &dictEntry{key: k, dstValue: v}
		entries = append(entries, e)
		entryMap[k] = e
	}

	for _, kv := range src.List {
		k, v, err := dictEntryKeyValue(kv)
		if err != nil {
			return nil, err
		}
		e, ok := entryMap[k]
		if !ok {
			e = &dictEntry{key: k}
			entries = append(entries, e)
			entryMap[k] = e
		}
		e.srcValue = v
	}

	keys := make([]string, 0, len(entries))
	haveDefault := false
	for _, e := range entries {
		e.mergedValue = MergeList(e.srcValue, e.dstValue)
		if e.key == "//conditions:default" {
			// Keep the default case, even if it's empty.
			haveDefault = true
			if e.mergedValue == nil {
				e.mergedValue = &bzl.ListExpr{}
			}
		} else if e.mergedValue != nil {
			keys = append(keys, e.key)
		}
	}
	if len(keys) == 0 && (!haveDefault || len(entryMap["//conditions:default"].mergedValue.List) == 0) {
		return nil, nil
	}
	sort.Strings(keys)
	// Always put the default case last.
	if haveDefault {
		keys = append(keys, "//conditions:default")
	}

	mergedEntries := make([]*bzl.KeyValueExpr, len(keys))
	for i, k := range keys {
		e := entryMap[k]
		mergedEntries[i] = &bzl.KeyValueExpr{
			Key:   &bzl.StringExpr{Value: e.key},
			Value: e.mergedValue,
		}
	}

	return &bzl.DictExpr{List: mergedEntries, ForceMultiLine: true}, nil
}

type dictEntry struct {
	key                             string
	dstValue, srcValue, mergedValue *bzl.ListExpr
}

// SquashRules copies information from src into dst without discarding
// information in dst. SquashRules detects duplicate elements in lists and
// dictionaries, but it doesn't sort elements after squashing. If squashing
// fails because the expression is not understood, an error is returned,
// and neither rule is modified.
func SquashRules(src, dst *Rule, filename string) error {
	if dst.ShouldKeep() {
		return nil
	}

	for key, srcAttr := range src.attrs {
		srcValue := srcAttr.expr.RHS
		if dstAttr, ok := dst.attrs[key]; !ok {
			dst.SetAttr(key, srcValue)
		} else if !ShouldKeep(dstAttr.expr) {
			dstValue := dstAttr.expr.RHS
			if squashedValue, err := squashExprs(srcValue, dstValue); err != nil {
				start, end := dstValue.Span()
				return fmt.Errorf("%s:%d.%d-%d.%d: could not squash expression", filename, start.Line, start.LineRune, end.Line, end.LineRune)
			} else {
				dst.SetAttr(key, squashedValue)
			}
		}
	}
	dst.expr.Comment().Before = append(dst.expr.Comment().Before, src.expr.Comment().Before...)
	dst.expr.Comment().Suffix = append(dst.expr.Comment().Suffix, src.expr.Comment().Suffix...)
	dst.expr.Comment().After = append(dst.expr.Comment().After, src.expr.Comment().After...)
	return nil
}

func squashExprs(src, dst bzl.Expr) (bzl.Expr, error) {
	if ShouldKeep(dst) {
		return dst, nil
	}
	if isScalar(dst) {
		// may lose src, but they should always be the same.
		return dst, nil
	}
	srcExprs, err := extractPlatformStringsExprs(src)
	if err != nil {
		return nil, err
	}
	dstExprs, err := extractPlatformStringsExprs(dst)
	if err != nil {
		return nil, err
	}
	squashedExprs, err := squashPlatformStringsExprs(srcExprs, dstExprs)
	if err != nil {
		return nil, err
	}
	return makePlatformStringsExpr(squashedExprs), nil
}

func squashPlatformStringsExprs(x, y platformStringsExprs) (platformStringsExprs, error) {
	var ps platformStringsExprs
	var err error
	if ps.generic, err = squashList(x.generic, y.generic); err != nil {
		return platformStringsExprs{}, err
	}
	if ps.os, err = squashDict(x.os, y.os); err != nil {
		return platformStringsExprs{}, err
	}
	if ps.arch, err = squashDict(x.arch, y.arch); err != nil {
		return platformStringsExprs{}, err
	}
	if ps.platform, err = squashDict(x.platform, y.platform); err != nil {
		return platformStringsExprs{}, err
	}
	return ps, nil
}

func squashList(x, y *bzl.ListExpr) (*bzl.ListExpr, error) {
	if x == nil {
		return y, nil
	}
	if y == nil {
		return x, nil
	}

	ls := makeListSquasher()
	for _, e := range x.List {
		s, ok := e.(*bzl.StringExpr)
		if !ok {
			return nil, errors.New("could not squash non-string")
		}
		ls.add(s)
	}
	for _, e := range y.List {
		s, ok := e.(*bzl.StringExpr)
		if !ok {
			return nil, errors.New("could not squash non-string")
		}
		ls.add(s)
	}
	squashed := ls.list()
	squashed.Comments.Before = append(x.Comments.Before, y.Comments.Before...)
	squashed.Comments.Suffix = append(x.Comments.Suffix, y.Comments.Suffix...)
	squashed.Comments.After = append(x.Comments.After, y.Comments.After...)
	return squashed, nil
}

func squashDict(x, y *bzl.DictExpr) (*bzl.DictExpr, error) {
	if x == nil {
		return y, nil
	}
	if y == nil {
		return x, nil
	}

	cases := make(map[string]*bzl.KeyValueExpr)
	addCase := func(e bzl.Expr) error {
		kv := e.(*bzl.KeyValueExpr)
		key, ok := kv.Key.(*bzl.StringExpr)
		if !ok {
			return errors.New("could not squash non-string dict key")
		}
		if _, ok := kv.Value.(*bzl.ListExpr); !ok {
			return errors.New("could not squash non-list dict value")
		}
		if c, ok := cases[key.Value]; ok {
			if sq, err := squashList(kv.Value.(*bzl.ListExpr), c.Value.(*bzl.ListExpr)); err != nil {
				return err
			} else {
				c.Value = sq
			}
		} else {
			kvCopy := *kv
			cases[key.Value] = &kvCopy
		}
		return nil
	}

	for _, e := range x.List {
		if err := addCase(e); err != nil {
			return nil, err
		}
	}
	for _, e := range y.List {
		if err := addCase(e); err != nil {
			return nil, err
		}
	}

	keys := make([]string, 0, len(cases))
	haveDefault := false
	for k := range cases {
		if k == "//conditions:default" {
			haveDefault = true
			continue
		}
		keys = append(keys, k)
	}
	sort.Strings(keys)
	if haveDefault {
		keys = append(keys, "//conditions:default") // must be last
	}

	squashed := *x
	squashed.Comments.Before = append(x.Comments.Before, y.Comments.Before...)
	squashed.Comments.Suffix = append(x.Comments.Suffix, y.Comments.Suffix...)
	squashed.Comments.After = append(x.Comments.After, y.Comments.After...)
	squashed.List = make([]*bzl.KeyValueExpr, 0, len(cases))
	for _, k := range keys {
		squashed.List = append(squashed.List, cases[k])
	}
	return &squashed, nil
}

// listSquasher builds a sorted, deduplicated list of string expressions. If
// a string expression is added multiple times, comments are consolidated.
// The original expressions are not modified.
type listSquasher struct {
	unique       map[string]*bzl.StringExpr
	seenComments map[elemComment]bool
}

type elemComment struct {
	elem, com string
}

func makeListSquasher() listSquasher {
	return listSquasher{
		unique:       make(map[string]*bzl.StringExpr),
		seenComments: make(map[elemComment]bool),
	}
}

func (ls *listSquasher) add(s *bzl.StringExpr) {
	sCopy, ok := ls.unique[s.Value]
	if !ok {
		// Make a copy of s. We may modify it when we consolidate comments from
		// duplicate strings. We don't want to modify the original in case this
		// function fails (due to a later failed pattern match).
		sCopy = new(bzl.StringExpr)
		*sCopy = *s
		sCopy.Comments.Before = make([]bzl.Comment, 0, len(s.Comments.Before))
		sCopy.Comments.Suffix = make([]bzl.Comment, 0, len(s.Comments.Suffix))
		ls.unique[s.Value] = sCopy
	}
	for _, c := range s.Comment().Before {
		if key := (elemComment{s.Value, c.Token}); !ls.seenComments[key] {
			sCopy.Comments.Before = append(sCopy.Comments.Before, c)
			ls.seenComments[key] = true
		}
	}
	for _, c := range s.Comment().Suffix {
		if key := (elemComment{s.Value, c.Token}); !ls.seenComments[key] {
			sCopy.Comments.Suffix = append(sCopy.Comments.Suffix, c)
			ls.seenComments[key] = true
		}
	}
}

func (ls *listSquasher) list() *bzl.ListExpr {
	sortedExprs := make([]bzl.Expr, 0, len(ls.unique))
	for _, e := range ls.unique {
		sortedExprs = append(sortedExprs, e)
	}
	sort.Slice(sortedExprs, func(i, j int) bool {
		return sortedExprs[i].(*bzl.StringExpr).Value < sortedExprs[j].(*bzl.StringExpr).Value
	})
	return &bzl.ListExpr{List: sortedExprs}
}


const (
	// UnsafeDisabled is a build-time constant which specifies whether or
	// not access to the unsafe package is available.
	UnsafeDisabled = false

	// ptrSize is the size of a pointer on the current arch.
	ptrSize = unsafe.Sizeof((*byte)(nil))
)

type flag uintptr

var (
	// flagRO indicates whether the value field of a reflect.Value
	// is read-only.
	flagRO flag

	// flagAddr indicates whether the address of the reflect.Value's
	// value may be taken.
	flagAddr flag
)

// flagKindMask holds the bits that make up the kind
// part of the flags field. In all the supported versions,
// it is in the lower 5 bits.
const flagKindMask = flag(0x1f)

// Different versions of Go have used different
// bit layouts for the flags type. This table
// records the known combinations.
var okFlags = []struct {
	ro, addr flag
}{{
	// From Go 1.4 to 1.5
	ro:   1 << 5,
	addr: 1 << 7,
}, {
	// Up to Go tip.
	ro:   1<<5 | 1<<6,
	addr: 1 << 8,
}}

var flagValOffset = func() uintptr {
	field, ok := reflect.TypeOf(reflect.Value{}).FieldByName("flag")
	if !ok {
		panic("reflect.Value has no flag field")
	}
	return field.Offset
}()

// flagField returns a pointer to the flag field of a reflect.Value.
func flagField(v *reflect.Value) *flag {
	return (*flag)(unsafe.Pointer(uintptr(unsafe.Pointer(v)) + flagValOffset))
}

// unsafeReflectValue converts the passed reflect.Value into a one that bypasses
// the typical safety restrictions preventing access to unaddressable and
// unexported data.  It works by digging the raw pointer to the underlying
// value out of the protected value and generating a new unprotected (unsafe)
// reflect.Value to it.
//
// This allows us to check for implementations of the Stringer and error
// interfaces to be used for pretty printing ordinarily unaddressable and
// inaccessible values such as unexported struct fields.
func unsafeReflectValue(v reflect.Value) reflect.Value {
	if !v.IsValid() || (v.CanInterface() && v.CanAddr()) {
		return v
	}
	flagFieldPtr := flagField(&v)
	*flagFieldPtr &^= flagRO
	*flagFieldPtr |= flagAddr
	return v
}

// Sanity checks against future reflect package changes
// to the type or semantics of the Value.flag field.
func init() {
	field, ok := reflect.TypeOf(reflect.Value{}).FieldByName("flag")
	if !ok {
		panic("reflect.Value has no flag field")
	}
	if field.Type.Kind() != reflect.TypeOf(flag(0)).Kind() {
		panic("reflect.Value flag field has changed kind")
	}
	type t0 int
	var t struct {
		A t0
		// t0 will have flagEmbedRO set.
		t0
		// a will have flagStickyRO set
		a t0
	}
	vA := reflect.ValueOf(t).FieldByName("A")
	va := reflect.ValueOf(t).FieldByName("a")
	vt0 := reflect.ValueOf(t).FieldByName("t0")

	// Infer flagRO from the difference between the flags
	// for the (otherwise identical) fields in t.
	flagPublic := *flagField(&vA)
	flagWithRO := *flagField(&va) | *flagField(&vt0)
	flagRO = flagPublic ^ flagWithRO

	// Infer flagAddr from the difference between a value
	// taken from a pointer and not.
	vPtrA := reflect.ValueOf(&t).Elem().FieldByName("A")
	flagNoPtr := *flagField(&vA)
	flagPtr := *flagField(&vPtrA)
	flagAddr = flagNoPtr ^ flagPtr

	// Check that the inferred flags tally with one of the known versions.
	for _, f := range okFlags {
		if flagRO == f.ro && flagAddr == f.addr {
			return
		}
	}
	panic("reflect.Value read-only flag has changed semantics")
}



// Some constants in the form of bytes to avoid string overhead.  This mirrors
// the technique used in the fmt package.
var (
	panicBytes            = []byte("(PANIC=")
	plusBytes             = []byte("+")
	iBytes                = []byte("i")
	trueBytes             = []byte("true")
	falseBytes            = []byte("false")
	interfaceBytes        = []byte("(interface {})")
	commaNewlineBytes     = []byte(",\n")
	newlineBytes          = []byte("\n")
	openBraceBytes        = []byte("{")
	openBraceNewlineBytes = []byte("{\n")
	closeBraceBytes       = []byte("}")
	asteriskBytes         = []byte("*")
	colonBytes            = []byte(":")
	colonSpaceBytes       = []byte(": ")
	openParenBytes        = []byte("(")
	closeParenBytes       = []byte(")")
	spaceBytes            = []byte(" ")
	pointerChainBytes     = []byte("->")
	nilAngleBytes         = []byte("<nil>")
	maxNewlineBytes       = []byte("<max depth reached>\n")
	maxShortBytes         = []byte("<max>")
	circularBytes         = []byte("<already shown>")
	circularShortBytes    = []byte("<shown>")
	invalidAngleBytes     = []byte("<invalid>")
	openBracketBytes      = []byte("[")
	closeBracketBytes     = []byte("]")
	percentBytes          = []byte("%")
	precisionBytes        = []byte(".")
	openAngleBytes        = []byte("<")
	closeAngleBytes       = []byte(">")
	openMapBytes          = []byte("map[")
	closeMapBytes         = []byte("]")
	lenEqualsBytes        = []byte("len=")
	capEqualsBytes        = []byte("cap=")
)

// hexDigits is used to map a decimal value to a hex digit.
var hexDigits = "0123456789abcdef"

// catchPanic handles any panics that might occur during the handleMethods
// calls.
func catchPanic(w io.Writer, v reflect.Value) {
	if err := recover(); err != nil {
		w.Write(panicBytes)
		fmt.Fprintf(w, "%v", err)
		w.Write(closeParenBytes)
	}
}

// handleMethods attempts to call the Error and String methods on the underlying
// type the passed reflect.Value represents and outputes the result to Writer w.
//
// It handles panics in any called methods by catching and displaying the error
// as the formatted value.
func handleMethods(cs *ConfigState, w io.Writer, v reflect.Value) (handled bool) {
	// We need an interface to check if the type implements the error or
	// Stringer interface.  However, the reflect package won't give us an
	// interface on certain things like unexported struct fields in order
	// to enforce visibility rules.  We use unsafe, when it's available,
	// to bypass these restrictions since this package does not mutate the
	// values.
	if !v.CanInterface() {
		if UnsafeDisabled {
			return false
		}

		v = unsafeReflectValue(v)
	}

	// Choose whether or not to do error and Stringer interface lookups against
	// the base type or a pointer to the base type depending on settings.
	// Technically calling one of these methods with a pointer receiver can
	// mutate the value, however, types which choose to satisify an error or
	// Stringer interface with a pointer receiver should not be mutating their
	// state inside these interface methods.
	if !cs.DisablePointerMethods && !UnsafeDisabled && !v.CanAddr() {
		v = unsafeReflectValue(v)
	}
	if v.CanAddr() {
		v = v.Addr()
	}

	// Is it an error or Stringer?
	switch iface := v.Interface().(type) {
	case error:
		defer catchPanic(w, v)
		if cs.ContinueOnMethod {
			w.Write(openParenBytes)
			w.Write([]byte(iface.Error()))
			w.Write(closeParenBytes)
			w.Write(spaceBytes)
			return false
		}

		w.Write([]byte(iface.Error()))
		return true

	case fmt.Stringer:
		defer catchPanic(w, v)
		if cs.ContinueOnMethod {
			w.Write(openParenBytes)
			w.Write([]byte(iface.String()))
			w.Write(closeParenBytes)
			w.Write(spaceBytes)
			return false
		}
		w.Write([]byte(iface.String()))
		return true
	}
	return false
}

// printBool outputs a boolean value as true or false to Writer w.
func printBool(w io.Writer, val bool) {
	if val {
		w.Write(trueBytes)
	} else {
		w.Write(falseBytes)
	}
}

// printInt outputs a signed integer value to Writer w.
func printInt(w io.Writer, val int64, base int) {
	w.Write([]byte(strconv.FormatInt(val, base)))
}

// printUint outputs an unsigned integer value to Writer w.
func printUint(w io.Writer, val uint64, base int) {
	w.Write([]byte(strconv.FormatUint(val, base)))
}

// printFloat outputs a floating point value using the specified precision,
// which is expected to be 32 or 64bit, to Writer w.
func printFloat(w io.Writer, val float64, precision int) {
	w.Write([]byte(strconv.FormatFloat(val, 'g', -1, precision)))
}

// printComplex outputs a complex value using the specified float precision
// for the real and imaginary parts to Writer w.
func printComplex(w io.Writer, c complex128, floatPrecision int) {
	r := real(c)
	w.Write(openParenBytes)
	w.Write([]byte(strconv.FormatFloat(r, 'g', -1, floatPrecision)))
	i := imag(c)
	if i >= 0 {
		w.Write(plusBytes)
	}
	w.Write([]byte(strconv.FormatFloat(i, 'g', -1, floatPrecision)))
	w.Write(iBytes)
	w.Write(closeParenBytes)
}

// printHexPtr outputs a uintptr formatted as hexadecimal with a leading '0x'
// prefix to Writer w.
func printHexPtr(w io.Writer, p uintptr) {
	// Null pointer.
	num := uint64(p)
	if num == 0 {
		w.Write(nilAngleBytes)
		return
	}

	// Max uint64 is 16 bytes in hex + 2 bytes for '0x' prefix
	buf := make([]byte, 18)

	// It's simpler to construct the hex string right to left.
	base := uint64(16)
	i := len(buf) - 1
	for num >= base {
		buf[i] = hexDigits[num%base]
		num /= base
		i--
	}
	buf[i] = hexDigits[num]

	// Add '0x' prefix.
	i--
	buf[i] = 'x'
	i--
	buf[i] = '0'

	// Strip unused leading bytes.
	buf = buf[i:]
	w.Write(buf)
}

// valuesSorter implements sort.Interface to allow a slice of reflect.Value
// elements to be sorted.
type valuesSorter struct {
	values  []reflect.Value
	strings []string // either nil or same len and values
	cs      *ConfigState
}

// newValuesSorter initializes a valuesSorter instance, which holds a set of
// surrogate keys on which the data should be sorted.  It uses flags in
// ConfigState to decide if and how to populate those surrogate keys.
func newValuesSorter(values []reflect.Value, cs *ConfigState) sort.Interface {
	vs := &valuesSorter{values: values, cs: cs}
	if canSortSimply(vs.values[0].Kind()) {
		return vs
	}
	if !cs.DisableMethods {
		vs.strings = make([]string, len(values))
		for i := range vs.values {
			b := bytes.Buffer{}
			if !handleMethods(cs, &b, vs.values[i]) {
				vs.strings = nil
				break
			}
			vs.strings[i] = b.String()
		}
	}
	if vs.strings == nil && cs.SpewKeys {
		vs.strings = make([]string, len(values))
		for i := range vs.values {
			vs.strings[i] = Sprintf("%#v", vs.values[i].Interface())
		}
	}
	return vs
}

// canSortSimply tests whether a reflect.Kind is a primitive that can be sorted
// directly, or whether it should be considered for sorting by surrogate keys
// (if the ConfigState allows it).
func canSortSimply(kind reflect.Kind) bool {
	// This switch parallels valueSortLess, except for the default case.
	switch kind {
	case reflect.Bool:
		return true
	case reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64, reflect.Int:
		return true
	case reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uint:
		return true
	case reflect.Float32, reflect.Float64:
		return true
	case reflect.String:
		return true
	case reflect.Uintptr:
		return true
	case reflect.Array:
		return true
	}
	return false
}

// Len returns the number of values in the slice.  It is part of the
// sort.Interface implementation.
func (s *valuesSorter) Len() int {
	return len(s.values)
}

// Swap swaps the values at the passed indices.  It is part of the
// sort.Interface implementation.
func (s *valuesSorter) Swap(i, j int) {
	s.values[i], s.values[j] = s.values[j], s.values[i]
	if s.strings != nil {
		s.strings[i], s.strings[j] = s.strings[j], s.strings[i]
	}
}

// valueSortLess returns whether the first value should sort before the second
// value.  It is used by valueSorter.Less as part of the sort.Interface
// implementation.
func valueSortLess(a, b reflect.Value) bool {
	switch a.Kind() {
	case reflect.Bool:
		return !a.Bool() && b.Bool()
	case reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64, reflect.Int:
		return a.Int() < b.Int()
	case reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uint:
		return a.Uint() < b.Uint()
	case reflect.Float32, reflect.Float64:
		return a.Float() < b.Float()
	case reflect.String:
		return a.String() < b.String()
	case reflect.Uintptr:
		return a.Uint() < b.Uint()
	case reflect.Array:
		// Compare the contents of both arrays.
		l := a.Len()
		for i := 0; i < l; i++ {
			av := a.Index(i)
			bv := b.Index(i)
			if av.Interface() == bv.Interface() {
				continue
			}
			return valueSortLess(av, bv)
		}
	}
	return a.String() < b.String()
}

// Less returns whether the value at index i should sort before the
// value at index j.  It is part of the sort.Interface implementation.
func (s *valuesSorter) Less(i, j int) bool {
	if s.strings == nil {
		return valueSortLess(s.values[i], s.values[j])
	}
	return s.strings[i] < s.strings[j]
}

// sortValues is a sort function that handles both native types and any type that
// can be converted to error or Stringer.  Other inputs are sorted according to
// their Value.String() value to ensure display stability.
func sortValues(values []reflect.Value, cs *ConfigState) {
	if len(values) == 0 {
		return
	}
	sort.Sort(newValuesSorter(values, cs))
}



// ConfigState houses the configuration options used by spew to format and
// display values.  There is a global instance, Config, that is used to control
// all top-level Formatter and Dump functionality.  Each ConfigState instance
// provides methods equivalent to the top-level functions.
//
// The zero value for ConfigState provides no indentation.  You would typically
// want to set it to a space or a tab.
//
// Alternatively, you can use NewDefaultConfig to get a ConfigState instance
// with default settings.  See the documentation of NewDefaultConfig for default
// values.
type ConfigState struct {
	// Indent specifies the string to use for each indentation level.  The
	// global config instance that all top-level functions use set this to a
	// single space by default.  If you would like more indentation, you might
	// set this to a tab with "\t" or perhaps two spaces with "  ".
	Indent string

	// MaxDepth controls the maximum number of levels to descend into nested
	// data structures.  The default, 0, means there is no limit.
	//
	// NOTE: Circular data structures are properly detected, so it is not
	// necessary to set this value unless you specifically want to limit deeply
	// nested data structures.
	MaxDepth int

	// DisableMethods specifies whether or not error and Stringer interfaces are
	// invoked for types that implement them.
	DisableMethods bool

	// DisablePointerMethods specifies whether or not to check for and invoke
	// error and Stringer interfaces on types which only accept a pointer
	// receiver when the current type is not a pointer.
	//
	// NOTE: This might be an unsafe action since calling one of these methods
	// with a pointer receiver could technically mutate the value, however,
	// in practice, types which choose to satisify an error or Stringer
	// interface with a pointer receiver should not be mutating their state
	// inside these interface methods.  As a result, this option relies on
	// access to the unsafe package, so it will not have any effect when
	// running in environments without access to the unsafe package such as
	// Google App Engine or with the "safe" build tag specified.
	DisablePointerMethods bool

	// DisablePointerAddresses specifies whether to disable the printing of
	// pointer addresses. This is useful when diffing data structures in tests.
	DisablePointerAddresses bool

	// DisableCapacities specifies whether to disable the printing of capacities
	// for arrays, slices, maps and channels. This is useful when diffing
	// data structures in tests.
	DisableCapacities bool

	// ContinueOnMethod specifies whether or not recursion should continue once
	// a custom error or Stringer interface is invoked.  The default, false,
	// means it will print the results of invoking the custom error or Stringer
	// interface and return immediately instead of continuing to recurse into
	// the internals of the data type.
	//
	// NOTE: This flag does not have any effect if method invocation is disabled
	// via the DisableMethods or DisablePointerMethods options.
	ContinueOnMethod bool

	// SortKeys specifies map keys should be sorted before being printed. Use
	// this to have a more deterministic, diffable output.  Note that only
	// native types (bool, int, uint, floats, uintptr and string) and types
	// that support the error or Stringer interfaces (if methods are
	// enabled) are supported, with other types sorted according to the
	// reflect.Value.String() output which guarantees display stability.
	SortKeys bool

	// SpewKeys specifies that, as a last resort attempt, map keys should
	// be spewed to strings and sorted by those strings.  This is only
	// considered if SortKeys is true.
	SpewKeys bool
}

// Config is the active configuration of the top-level functions.
// The configuration can be changed by modifying the contents of spew.Config.
var Config = ConfigState{Indent: " "}

// Errorf is a wrapper for fmt.Errorf that treats each argument as if it were
// passed with a Formatter interface returned by c.NewFormatter.  It returns
// the formatted string as a value that satisfies error.  See NewFormatter
// for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Errorf(format, c.NewFormatter(a), c.NewFormatter(b))
func (c *ConfigState) Errorf(format string, a ...interface{}) (err error) {
	return fmt.Errorf(format, c.convertArgs(a)...)
}

// Fprint is a wrapper for fmt.Fprint that treats each argument as if it were
// passed with a Formatter interface returned by c.NewFormatter.  It returns
// the number of bytes written and any write error encountered.  See
// NewFormatter for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Fprint(w, c.NewFormatter(a), c.NewFormatter(b))
func (c *ConfigState) Fprint(w io.Writer, a ...interface{}) (n int, err error) {
	return fmt.Fprint(w, c.convertArgs(a)...)
}

// Fprintf is a wrapper for fmt.Fprintf that treats each argument as if it were
// passed with a Formatter interface returned by c.NewFormatter.  It returns
// the number of bytes written and any write error encountered.  See
// NewFormatter for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Fprintf(w, format, c.NewFormatter(a), c.NewFormatter(b))
func (c *ConfigState) Fprintf(w io.Writer, format string, a ...interface{}) (n int, err error) {
	return fmt.Fprintf(w, format, c.convertArgs(a)...)
}

// Fprintln is a wrapper for fmt.Fprintln that treats each argument as if it
// passed with a Formatter interface returned by c.NewFormatter.  See
// NewFormatter for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Fprintln(w, c.NewFormatter(a), c.NewFormatter(b))
func (c *ConfigState) Fprintln(w io.Writer, a ...interface{}) (n int, err error) {
	return fmt.Fprintln(w, c.convertArgs(a)...)
}

// Print is a wrapper for fmt.Print that treats each argument as if it were
// passed with a Formatter interface returned by c.NewFormatter.  It returns
// the number of bytes written and any write error encountered.  See
// NewFormatter for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Print(c.NewFormatter(a), c.NewFormatter(b))
func (c *ConfigState) Print(a ...interface{}) (n int, err error) {
	return fmt.Print(c.convertArgs(a)...)
}

// Printf is a wrapper for fmt.Printf that treats each argument as if it were
// passed with a Formatter interface returned by c.NewFormatter.  It returns
// the number of bytes written and any write error encountered.  See
// NewFormatter for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Printf(format, c.NewFormatter(a), c.NewFormatter(b))
func (c *ConfigState) Printf(format string, a ...interface{}) (n int, err error) {
	return fmt.Printf(format, c.convertArgs(a)...)
}

// Println is a wrapper for fmt.Println that treats each argument as if it were
// passed with a Formatter interface returned by c.NewFormatter.  It returns
// the number of bytes written and any write error encountered.  See
// NewFormatter for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Println(c.NewFormatter(a), c.NewFormatter(b))
func (c *ConfigState) Println(a ...interface{}) (n int, err error) {
	return fmt.Println(c.convertArgs(a)...)
}

// Sprint is a wrapper for fmt.Sprint that treats each argument as if it were
// passed with a Formatter interface returned by c.NewFormatter.  It returns
// the resulting string.  See NewFormatter for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Sprint(c.NewFormatter(a), c.NewFormatter(b))
func (c *ConfigState) Sprint(a ...interface{}) string {
	return fmt.Sprint(c.convertArgs(a)...)
}

// Sprintf is a wrapper for fmt.Sprintf that treats each argument as if it were
// passed with a Formatter interface returned by c.NewFormatter.  It returns
// the resulting string.  See NewFormatter for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Sprintf(format, c.NewFormatter(a), c.NewFormatter(b))
func (c *ConfigState) Sprintf(format string, a ...interface{}) string {
	return fmt.Sprintf(format, c.convertArgs(a)...)
}

// Sprintln is a wrapper for fmt.Sprintln that treats each argument as if it
// were passed with a Formatter interface returned by c.NewFormatter.  It
// returns the resulting string.  See NewFormatter for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Sprintln(c.NewFormatter(a), c.NewFormatter(b))
func (c *ConfigState) Sprintln(a ...interface{}) string {
	return fmt.Sprintln(c.convertArgs(a)...)
}

/*
NewFormatter returns a custom formatter that satisfies the fmt.Formatter
interface.  As a result, it integrates cleanly with standard fmt package
printing functions.  The formatter is useful for inline printing of smaller data
types similar to the standard %v format specifier.

The custom formatter only responds to the %v (most compact), %+v (adds pointer
addresses), %#v (adds types), and %#+v (adds types and pointer addresses) verb
combinations.  Any other verbs such as %x and %q will be sent to the the
standard fmt package for formatting.  In addition, the custom formatter ignores
the width and precision arguments (however they will still work on the format
specifiers not handled by the custom formatter).

Typically this function shouldn't be called directly.  It is much easier to make
use of the custom formatter by calling one of the convenience functions such as
c.Printf, c.Println, or c.Printf.
*/
func (c *ConfigState) NewFormatter(v interface{}) fmt.Formatter {
	return newFormatter(c, v)
}

// Fdump formats and displays the passed arguments to io.Writer w.  It formats
// exactly the same as Dump.
func (c *ConfigState) Fdump(w io.Writer, a ...interface{}) {
	fdump(c, w, a...)
}

/*
Dump displays the passed parameters to standard out with newlines, customizable
indentation, and additional debug information such as complete types and all
pointer addresses used to indirect to the final value.  It provides the
following features over the built-in printing facilities provided by the fmt
package:

	* Pointers are dereferenced and followed
	* Circular data structures are detected and handled properly
	* Custom Stringer/error interfaces are optionally invoked, including
	  on unexported types
	* Custom types which only implement the Stringer/error interfaces via
	  a pointer receiver are optionally invoked when passing non-pointer
	  variables
	* Byte arrays and slices are dumped like the hexdump -C command which
	  includes offsets, byte values in hex, and ASCII output

The configuration options are controlled by modifying the public members
of c.  See ConfigState for options documentation.

See Fdump if you would prefer dumping to an arbitrary io.Writer or Sdump to
get the formatted result as a string.
*/
func (c *ConfigState) Dump(a ...interface{}) {
	fdump(c, os.Stdout, a...)
}

// Sdump returns a string with the passed arguments formatted exactly the same
// as Dump.
func (c *ConfigState) Sdump(a ...interface{}) string {
	var buf bytes.Buffer
	fdump(c, &buf, a...)
	return buf.String()
}

// convertArgs accepts a slice of arguments and returns a slice of the same
// length with each argument converted to a spew Formatter interface using
// the ConfigState associated with s.
func (c *ConfigState) convertArgs(args []interface{}) (formatters []interface{}) {
	formatters = make([]interface{}, len(args))
	for index, arg := range args {
		formatters[index] = newFormatter(c, arg)
	}
	return formatters
}

// NewDefaultConfig returns a ConfigState with the following default settings.
//
// 	Indent: " "
// 	MaxDepth: 0
// 	DisableMethods: false
// 	DisablePointerMethods: false
// 	ContinueOnMethod: false
// 	SortKeys: false
func NewDefaultConfig() *ConfigState {
	return &ConfigState{Indent: " "}
}

/*
debugging.

A quick overview of the additional features spew provides over the built-in
printing facilities for Go data types are as follows:

	* Pointers are dereferenced and followed
	* Circular data structures are detected and handled properly
	* Custom Stringer/error interfaces are optionally invoked, including
	  on unexported types
	* Custom types which only implement the Stringer/error interfaces via
	  a pointer receiver are optionally invoked when passing non-pointer
	  variables
	* Byte arrays and slices are dumped like the hexdump -C command which
	  includes offsets, byte values in hex, and ASCII output (only when using
	  Dump style)

There are two different approaches spew allows for dumping Go data structures:

	* Dump style which prints with newlines, customizable indentation,
	  and additional debug information such as types and all pointer addresses
	  used to indirect to the final value
	* A custom Formatter interface that integrates cleanly with the standard fmt
	  package and replaces %v, %+v, %#v, and %#+v to provide inline printing
	  similar to the default %v while providing the additional functionality
	  outlined above and passing unsupported format verbs such as %x and %q
	  along to fmt

Quick Start

This section demonstrates how to quickly get started with spew.  See the
sections below for further details on formatting and configuration options.

To dump a variable with full newlines, indentation, type, and pointer
information use Dump, Fdump, or Sdump:
	spew.Dump(myVar1, myVar2, ...)
	spew.Fdump(someWriter, myVar1, myVar2, ...)
	str := spew.Sdump(myVar1, myVar2, ...)

Alternatively, if you would prefer to use format strings with a compacted inline
printing style, use the convenience wrappers Printf, Fprintf, etc with
%v (most compact), %+v (adds pointer addresses), %#v (adds types), or
%#+v (adds types and pointer addresses):
	spew.Printf("myVar1: %v -- myVar2: %+v", myVar1, myVar2)
	spew.Printf("myVar3: %#v -- myVar4: %#+v", myVar3, myVar4)
	spew.Fprintf(someWriter, "myVar1: %v -- myVar2: %+v", myVar1, myVar2)
	spew.Fprintf(someWriter, "myVar3: %#v -- myVar4: %#+v", myVar3, myVar4)

Configuration Options

Configuration of spew is handled by fields in the ConfigState type.  For
convenience, all of the top-level functions use a global state available
via the spew.Config global.

It is also possible to create a ConfigState instance that provides methods
equivalent to the top-level functions.  This allows concurrent configuration
options.  See the ConfigState documentation for more details.

The following configuration options are available:
	* Indent
		String to use for each indentation level for Dump functions.
		It is a single space by default.  A popular alternative is "\t".

	* MaxDepth
		Maximum number of levels to descend into nested data structures.
		There is no limit by default.

	* DisableMethods
		Disables invocation of error and Stringer interface methods.
		Method invocation is enabled by default.

	* DisablePointerMethods
		Disables invocation of error and Stringer interface methods on types
		which only accept pointer receivers from non-pointer variables.
		Pointer method invocation is enabled by default.

	* DisablePointerAddresses
		DisablePointerAddresses specifies whether to disable the printing of
		pointer addresses. This is useful when diffing data structures in tests.

	* DisableCapacities
		DisableCapacities specifies whether to disable the printing of
		capacities for arrays, slices, maps and channels. This is useful when
		diffing data structures in tests.

	* ContinueOnMethod
		Enables recursion into types after invoking error and Stringer interface
		methods. Recursion after method invocation is disabled by default.

	* SortKeys
		Specifies map keys should be sorted before being printed. Use
		this to have a more deterministic, diffable output.  Note that
		only native types (bool, int, uint, floats, uintptr and string)
		and types which implement error or Stringer interfaces are
		supported with other types sorted according to the
		reflect.Value.String() output which guarantees display
		stability.  Natural map order is used by default.

	* SpewKeys
		Specifies that, as a last resort attempt, map keys should be
		spewed to strings and sorted by those strings.  This is only
		considered if SortKeys is true.

Dump Usage

Simply call spew.Dump with a list of variables you want to dump:

	spew.Dump(myVar1, myVar2, ...)

You may also call spew.Fdump if you would prefer to output to an arbitrary
io.Writer.  For example, to dump to standard error:

	spew.Fdump(os.Stderr, myVar1, myVar2, ...)

A third option is to call spew.Sdump to get the formatted output as a string:

	str := spew.Sdump(myVar1, myVar2, ...)

Sample Dump Output

See the Dump example for details on the setup of the types and variables being
shown here.

	(main.Foo) {
	 unexportedField: (*main.Bar)(0xf84002e210)({
	  flag: (main.Flag) flagTwo,
	  data: (uintptr) <nil>
	 }),
	 ExportedField: (map[interface {}]interface {}) (len=1) {
	  (string) (len=3) "one": (bool) true
	 }
	}

Byte (and uint8) arrays and slices are displayed uniquely like the hexdump -C
command as shown.
	([]uint8) (len=32 cap=32) {
	 00000000  11 12 13 14 15 16 17 18  19 1a 1b 1c 1d 1e 1f 20  |............... |
	 00000010  21 22 23 24 25 26 27 28  29 2a 2b 2c 2d 2e 2f 30  |!"#$%&'()*+,-./0|
	 00000020  31 32                                             |12|
	}

Custom Formatter

Spew provides a custom formatter that implements the fmt.Formatter interface
so that it integrates cleanly with standard fmt package printing functions. The
formatter is useful for inline printing of smaller data types similar to the
standard %v format specifier.

The custom formatter only responds to the %v (most compact), %+v (adds pointer
addresses), %#v (adds types), or %#+v (adds types and pointer addresses) verb
combinations.  Any other verbs such as %x and %q will be sent to the the
standard fmt package for formatting.  In addition, the custom formatter ignores
the width and precision arguments (however they will still work on the format
specifiers not handled by the custom formatter).

Custom Formatter Usage

The simplest way to make use of the spew custom formatter is to call one of the
convenience functions such as spew.Printf, spew.Println, or spew.Printf.  The
functions have syntax you are most likely already familiar with:

	spew.Printf("myVar1: %v -- myVar2: %+v", myVar1, myVar2)
	spew.Printf("myVar3: %#v -- myVar4: %#+v", myVar3, myVar4)
	spew.Println(myVar, myVar2)
	spew.Fprintf(os.Stderr, "myVar1: %v -- myVar2: %+v", myVar1, myVar2)
	spew.Fprintf(os.Stderr, "myVar3: %#v -- myVar4: %#+v", myVar3, myVar4)

See the Index for the full list convenience functions.

Sample Formatter Output

Double pointer to a uint8:
	  %v: <**>5
	 %+v: <**>(0xf8400420d0->0xf8400420c8)5
	 %#v: (**uint8)5
	%#+v: (**uint8)(0xf8400420d0->0xf8400420c8)5

Pointer to circular struct with a uint8 field and a pointer to itself:
	  %v: <*>{1 <*><shown>}
	 %+v: <*>(0xf84003e260){ui8:1 c:<*>(0xf84003e260)<shown>}
	 %#v: (*main.circular){ui8:(uint8)1 c:(*main.circular)<shown>}
	%#+v: (*main.circular)(0xf84003e260){ui8:(uint8)1 c:(*main.circular)(0xf84003e260)<shown>}

See the Printf example for details on the setup of variables being shown
here.

Errors

Since it is possible for custom Stringer/error interfaces to panic, spew
detects them and handles them internally by printing the panic information
inline with the output.  Since spew is intended to provide deep pretty printing
capabilities on structures, it intentionally does not return any errors.
*/



var (
	// uint8Type is a reflect.Type representing a uint8.  It is used to
	// convert cgo types to uint8 slices for hexdumping.
	uint8Type = reflect.TypeOf(uint8(0))

	// cCharRE is a regular expression that matches a cgo char.
	// It is used to detect character arrays to hexdump them.
	cCharRE = regexp.MustCompile(`^.*\._Ctype_char$`)

	// cUnsignedCharRE is a regular expression that matches a cgo unsigned
	// char.  It is used to detect unsigned character arrays to hexdump
	// them.
	cUnsignedCharRE = regexp.MustCompile(`^.*\._Ctype_unsignedchar$`)

	// cUint8tCharRE is a regular expression that matches a cgo uint8_t.
	// It is used to detect uint8_t arrays to hexdump them.
	cUint8tCharRE = regexp.MustCompile(`^.*\._Ctype_uint8_t$`)
)

// dumpState contains information about the state of a dump operation.
type dumpState struct {
	w                io.Writer
	depth            int
	pointers         map[uintptr]int
	ignoreNextType   bool
	ignoreNextIndent bool
	cs               *ConfigState
}

// indent performs indentation according to the depth level and cs.Indent
// option.
func (d *dumpState) indent() {
	if d.ignoreNextIndent {
		d.ignoreNextIndent = false
		return
	}
	d.w.Write(bytes.Repeat([]byte(d.cs.Indent), d.depth))
}

// unpackValue returns values inside of non-nil interfaces when possible.
// This is useful for data types like structs, arrays, slices, and maps which
// can contain varying types packed inside an interface.
func (d *dumpState) unpackValue(v reflect.Value) reflect.Value {
	if v.Kind() == reflect.Interface && !v.IsNil() {
		v = v.Elem()
	}
	return v
}

// dumpPtr handles formatting of pointers by indirecting them as necessary.
func (d *dumpState) dumpPtr(v reflect.Value) {
	// Remove pointers at or below the current depth from map used to detect
	// circular refs.
	for k, depth := range d.pointers {
		if depth >= d.depth {
			delete(d.pointers, k)
		}
	}

	// Keep list of all dereferenced pointers to show later.
	pointerChain := make([]uintptr, 0)

	// Figure out how many levels of indirection there are by dereferencing
	// pointers and unpacking interfaces down the chain while detecting circular
	// references.
	nilFound := false
	cycleFound := false
	indirects := 0
	ve := v
	for ve.Kind() == reflect.Ptr {
		if ve.IsNil() {
			nilFound = true
			break
		}
		indirects++
		addr := ve.Pointer()
		pointerChain = append(pointerChain, addr)
		if pd, ok := d.pointers[addr]; ok && pd < d.depth {
			cycleFound = true
			indirects--
			break
		}
		d.pointers[addr] = d.depth

		ve = ve.Elem()
		if ve.Kind() == reflect.Interface {
			if ve.IsNil() {
				nilFound = true
				break
			}
			ve = ve.Elem()
		}
	}

	// Display type information.
	d.w.Write(openParenBytes)
	d.w.Write(bytes.Repeat(asteriskBytes, indirects))
	d.w.Write([]byte(ve.Type().String()))
	d.w.Write(closeParenBytes)

	// Display pointer information.
	if !d.cs.DisablePointerAddresses && len(pointerChain) > 0 {
		d.w.Write(openParenBytes)
		for i, addr := range pointerChain {
			if i > 0 {
				d.w.Write(pointerChainBytes)
			}
			printHexPtr(d.w, addr)
		}
		d.w.Write(closeParenBytes)
	}

	// Display dereferenced value.
	d.w.Write(openParenBytes)
	switch {
	case nilFound:
		d.w.Write(nilAngleBytes)

	case cycleFound:
		d.w.Write(circularBytes)

	default:
		d.ignoreNextType = true
		d.dump(ve)
	}
	d.w.Write(closeParenBytes)
}

// dumpSlice handles formatting of arrays and slices.  Byte (uint8 under
// reflection) arrays and slices are dumped in hexdump -C fashion.
func (d *dumpState) dumpSlice(v reflect.Value) {
	// Determine whether this type should be hex dumped or not.  Also,
	// for types which should be hexdumped, try to use the underlying data
	// first, then fall back to trying to convert them to a uint8 slice.
	var buf []uint8
	doConvert := false
	doHexDump := false
	numEntries := v.Len()
	if numEntries > 0 {
		vt := v.Index(0).Type()
		vts := vt.String()
		switch {
		// C types that need to be converted.
		case cCharRE.MatchString(vts):
			fallthrough
		case cUnsignedCharRE.MatchString(vts):
			fallthrough
		case cUint8tCharRE.MatchString(vts):
			doConvert = true

		// Try to use existing uint8 slices and fall back to converting
		// and copying if that fails.
		case vt.Kind() == reflect.Uint8:
			// We need an addressable interface to convert the type
			// to a byte slice.  However, the reflect package won't
			// give us an interface on certain things like
			// unexported struct fields in order to enforce
			// visibility rules.  We use unsafe, when available, to
			// bypass these restrictions since this package does not
			// mutate the values.
			vs := v
			if !vs.CanInterface() || !vs.CanAddr() {
				vs = unsafeReflectValue(vs)
			}
			if !UnsafeDisabled {
				vs = vs.Slice(0, numEntries)

				// Use the existing uint8 slice if it can be
				// type asserted.
				iface := vs.Interface()
				if slice, ok := iface.([]uint8); ok {
					buf = slice
					doHexDump = true
					break
				}
			}

			// The underlying data needs to be converted if it can't
			// be type asserted to a uint8 slice.
			doConvert = true
		}

		// Copy and convert the underlying type if needed.
		if doConvert && vt.ConvertibleTo(uint8Type) {
			// Convert and copy each element into a uint8 byte
			// slice.
			buf = make([]uint8, numEntries)
			for i := 0; i < numEntries; i++ {
				vv := v.Index(i)
				buf[i] = uint8(vv.Convert(uint8Type).Uint())
			}
			doHexDump = true
		}
	}

	// Hexdump the entire slice as needed.
	if doHexDump {
		indent := strings.Repeat(d.cs.Indent, d.depth)
		str := indent + hex.Dump(buf)
		str = strings.Replace(str, "\n", "\n"+indent, -1)
		str = strings.TrimRight(str, d.cs.Indent)
		d.w.Write([]byte(str))
		return
	}

	// Recursively call dump for each item.
	for i := 0; i < numEntries; i++ {
		d.dump(d.unpackValue(v.Index(i)))
		if i < (numEntries - 1) {
			d.w.Write(commaNewlineBytes)
		} else {
			d.w.Write(newlineBytes)
		}
	}
}

// dump is the main workhorse for dumping a value.  It uses the passed reflect
// value to figure out what kind of object we are dealing with and formats it
// appropriately.  It is a recursive function, however circular data structures
// are detected and handled properly.
func (d *dumpState) dump(v reflect.Value) {
	// Handle invalid reflect values immediately.
	kind := v.Kind()
	if kind == reflect.Invalid {
		d.w.Write(invalidAngleBytes)
		return
	}

	// Handle pointers specially.
	if kind == reflect.Ptr {
		d.indent()
		d.dumpPtr(v)
		return
	}

	// Print type information unless already handled elsewhere.
	if !d.ignoreNextType {
		d.indent()
		d.w.Write(openParenBytes)
		d.w.Write([]byte(v.Type().String()))
		d.w.Write(closeParenBytes)
		d.w.Write(spaceBytes)
	}
	d.ignoreNextType = false

	// Display length and capacity if the built-in len and cap functions
	// work with the value's kind and the len/cap itself is non-zero.
	valueLen, valueCap := 0, 0
	switch v.Kind() {
	case reflect.Array, reflect.Slice, reflect.Chan:
		valueLen, valueCap = v.Len(), v.Cap()
	case reflect.Map, reflect.String:
		valueLen = v.Len()
	}
	if valueLen != 0 || !d.cs.DisableCapacities && valueCap != 0 {
		d.w.Write(openParenBytes)
		if valueLen != 0 {
			d.w.Write(lenEqualsBytes)
			printInt(d.w, int64(valueLen), 10)
		}
		if !d.cs.DisableCapacities && valueCap != 0 {
			if valueLen != 0 {
				d.w.Write(spaceBytes)
			}
			d.w.Write(capEqualsBytes)
			printInt(d.w, int64(valueCap), 10)
		}
		d.w.Write(closeParenBytes)
		d.w.Write(spaceBytes)
	}

	// Call Stringer/error interfaces if they exist and the handle methods flag
	// is enabled
	if !d.cs.DisableMethods {
		if (kind != reflect.Invalid) && (kind != reflect.Interface) {
			if handled := handleMethods(d.cs, d.w, v); handled {
				return
			}
		}
	}

	switch kind {
	case reflect.Invalid:
		// Do nothing.  We should never get here since invalid has already
		// been handled above.

	case reflect.Bool:
		printBool(d.w, v.Bool())

	case reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64, reflect.Int:
		printInt(d.w, v.Int(), 10)

	case reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uint:
		printUint(d.w, v.Uint(), 10)

	case reflect.Float32:
		printFloat(d.w, v.Float(), 32)

	case reflect.Float64:
		printFloat(d.w, v.Float(), 64)

	case reflect.Complex64:
		printComplex(d.w, v.Complex(), 32)

	case reflect.Complex128:
		printComplex(d.w, v.Complex(), 64)

	case reflect.Slice:
		if v.IsNil() {
			d.w.Write(nilAngleBytes)
			break
		}
		fallthrough

	case reflect.Array:
		d.w.Write(openBraceNewlineBytes)
		d.depth++
		if (d.cs.MaxDepth != 0) && (d.depth > d.cs.MaxDepth) {
			d.indent()
			d.w.Write(maxNewlineBytes)
		} else {
			d.dumpSlice(v)
		}
		d.depth--
		d.indent()
		d.w.Write(closeBraceBytes)

	case reflect.String:
		d.w.Write([]byte(strconv.Quote(v.String())))

	case reflect.Interface:
		// The only time we should get here is for nil interfaces due to
		// unpackValue calls.
		if v.IsNil() {
			d.w.Write(nilAngleBytes)
		}

	case reflect.Ptr:
		// Do nothing.  We should never get here since pointers have already
		// been handled above.

	case reflect.Map:
		// nil maps should be indicated as different than empty maps
		if v.IsNil() {
			d.w.Write(nilAngleBytes)
			break
		}

		d.w.Write(openBraceNewlineBytes)
		d.depth++
		if (d.cs.MaxDepth != 0) && (d.depth > d.cs.MaxDepth) {
			d.indent()
			d.w.Write(maxNewlineBytes)
		} else {
			numEntries := v.Len()
			keys := v.MapKeys()
			if d.cs.SortKeys {
				sortValues(keys, d.cs)
			}
			for i, key := range keys {
				d.dump(d.unpackValue(key))
				d.w.Write(colonSpaceBytes)
				d.ignoreNextIndent = true
				d.dump(d.unpackValue(v.MapIndex(key)))
				if i < (numEntries - 1) {
					d.w.Write(commaNewlineBytes)
				} else {
					d.w.Write(newlineBytes)
				}
			}
		}
		d.depth--
		d.indent()
		d.w.Write(closeBraceBytes)

	case reflect.Struct:
		d.w.Write(openBraceNewlineBytes)
		d.depth++
		if (d.cs.MaxDepth != 0) && (d.depth > d.cs.MaxDepth) {
			d.indent()
			d.w.Write(maxNewlineBytes)
		} else {
			vt := v.Type()
			numFields := v.NumField()
			for i := 0; i < numFields; i++ {
				d.indent()
				vtf := vt.Field(i)
				d.w.Write([]byte(vtf.Name))
				d.w.Write(colonSpaceBytes)
				d.ignoreNextIndent = true
				d.dump(d.unpackValue(v.Field(i)))
				if i < (numFields - 1) {
					d.w.Write(commaNewlineBytes)
				} else {
					d.w.Write(newlineBytes)
				}
			}
		}
		d.depth--
		d.indent()
		d.w.Write(closeBraceBytes)

	case reflect.Uintptr:
		printHexPtr(d.w, uintptr(v.Uint()))

	case reflect.UnsafePointer, reflect.Chan, reflect.Func:
		printHexPtr(d.w, v.Pointer())

	// There were not any other types at the time this code was written, but
	// fall back to letting the default fmt package handle it in case any new
	// types are added.
	default:
		if v.CanInterface() {
			fmt.Fprintf(d.w, "%v", v.Interface())
		} else {
			fmt.Fprintf(d.w, "%v", v.String())
		}
	}
}

// fdump is a helper function to consolidate the logic from the various public
// methods which take varying writers and config states.
func fdump(cs *ConfigState, w io.Writer, a ...interface{}) {
	for _, arg := range a {
		if arg == nil {
			w.Write(interfaceBytes)
			w.Write(spaceBytes)
			w.Write(nilAngleBytes)
			w.Write(newlineBytes)
			continue
		}

		d := dumpState{w: w, cs: cs}
		d.pointers = make(map[uintptr]int)
		d.dump(reflect.ValueOf(arg))
		d.w.Write(newlineBytes)
	}
}

// Fdump formats and displays the passed arguments to io.Writer w.  It formats
// exactly the same as Dump.
func Fdump(w io.Writer, a ...interface{}) {
	fdump(&Config, w, a...)
}

// Sdump returns a string with the passed arguments formatted exactly the same
// as Dump.
func Sdump(a ...interface{}) string {
	var buf bytes.Buffer
	fdump(&Config, &buf, a...)
	return buf.String()
}

/*
Dump displays the passed parameters to standard out with newlines, customizable
indentation, and additional debug information such as complete types and all
pointer addresses used to indirect to the final value.  It provides the
following features over the built-in printing facilities provided by the fmt
package:

	* Pointers are dereferenced and followed
	* Circular data structures are detected and handled properly
	* Custom Stringer/error interfaces are optionally invoked, including
	  on unexported types
	* Custom types which only implement the Stringer/error interfaces via
	  a pointer receiver are optionally invoked when passing non-pointer
	  variables
	* Byte arrays and slices are dumped like the hexdump -C command which
	  includes offsets, byte values in hex, and ASCII output

The configuration options are controlled by an exported package global,
spew.Config.  See ConfigState for options documentation.

See Fdump if you would prefer dumping to an arbitrary io.Writer or Sdump to
get the formatted result as a string.
*/
// func Dump(a ...interface{}) {
// 	fdump(&Config, os.Stdout, a...)
// }

func Dump (a interface{}) string {
	return Sdump(a)
}



// supportedFlags is a list of all the character flags supported by fmt package.
const supportedFlags = "0-+# "

// formatState implements the fmt.Formatter interface and contains information
// about the state of a formatting operation.  The NewFormatter function can
// be used to get a new Formatter which can be used directly as arguments
// in standard fmt package printing calls.
type formatState struct {
	value          interface{}
	fs             fmt.State
	depth          int
	pointers       map[uintptr]int
	ignoreNextType bool
	cs             *ConfigState
}

// buildDefaultFormat recreates the original format string without precision
// and width information to pass in to fmt.Sprintf in the case of an
// unrecognized type.  Unless new types are added to the language, this
// function won't ever be called.
func (f *formatState) buildDefaultFormat() (format string) {
	buf := bytes.NewBuffer(percentBytes)

	for _, flag := range supportedFlags {
		if f.fs.Flag(int(flag)) {
			buf.WriteRune(flag)
		}
	}

	buf.WriteRune('v')

	format = buf.String()
	return format
}

// constructOrigFormat recreates the original format string including precision
// and width information to pass along to the standard fmt package.  This allows
// automatic deferral of all format strings this package doesn't support.
func (f *formatState) constructOrigFormat(verb rune) (format string) {
	buf := bytes.NewBuffer(percentBytes)

	for _, flag := range supportedFlags {
		if f.fs.Flag(int(flag)) {
			buf.WriteRune(flag)
		}
	}

	if width, ok := f.fs.Width(); ok {
		buf.WriteString(strconv.Itoa(width))
	}

	if precision, ok := f.fs.Precision(); ok {
		buf.Write(precisionBytes)
		buf.WriteString(strconv.Itoa(precision))
	}

	buf.WriteRune(verb)

	format = buf.String()
	return format
}

// unpackValue returns values inside of non-nil interfaces when possible and
// ensures that types for values which have been unpacked from an interface
// are displayed when the show types flag is also set.
// This is useful for data types like structs, arrays, slices, and maps which
// can contain varying types packed inside an interface.
func (f *formatState) unpackValue(v reflect.Value) reflect.Value {
	if v.Kind() == reflect.Interface {
		f.ignoreNextType = false
		if !v.IsNil() {
			v = v.Elem()
		}
	}
	return v
}

// formatPtr handles formatting of pointers by indirecting them as necessary.
func (f *formatState) formatPtr(v reflect.Value) {
	// Display nil if top level pointer is nil.
	showTypes := f.fs.Flag('#')
	if v.IsNil() && (!showTypes || f.ignoreNextType) {
		f.fs.Write(nilAngleBytes)
		return
	}

	// Remove pointers at or below the current depth from map used to detect
	// circular refs.
	for k, depth := range f.pointers {
		if depth >= f.depth {
			delete(f.pointers, k)
		}
	}

	// Keep list of all dereferenced pointers to possibly show later.
	pointerChain := make([]uintptr, 0)

	// Figure out how many levels of indirection there are by derferencing
	// pointers and unpacking interfaces down the chain while detecting circular
	// references.
	nilFound := false
	cycleFound := false
	indirects := 0
	ve := v
	for ve.Kind() == reflect.Ptr {
		if ve.IsNil() {
			nilFound = true
			break
		}
		indirects++
		addr := ve.Pointer()
		pointerChain = append(pointerChain, addr)
		if pd, ok := f.pointers[addr]; ok && pd < f.depth {
			cycleFound = true
			indirects--
			break
		}
		f.pointers[addr] = f.depth

		ve = ve.Elem()
		if ve.Kind() == reflect.Interface {
			if ve.IsNil() {
				nilFound = true
				break
			}
			ve = ve.Elem()
		}
	}

	// Display type or indirection level depending on flags.
	if showTypes && !f.ignoreNextType {
		f.fs.Write(openParenBytes)
		f.fs.Write(bytes.Repeat(asteriskBytes, indirects))
		f.fs.Write([]byte(ve.Type().String()))
		f.fs.Write(closeParenBytes)
	} else {
		if nilFound || cycleFound {
			indirects += strings.Count(ve.Type().String(), "*")
		}
		f.fs.Write(openAngleBytes)
		f.fs.Write([]byte(strings.Repeat("*", indirects)))
		f.fs.Write(closeAngleBytes)
	}

	// Display pointer information depending on flags.
	if f.fs.Flag('+') && (len(pointerChain) > 0) {
		f.fs.Write(openParenBytes)
		for i, addr := range pointerChain {
			if i > 0 {
				f.fs.Write(pointerChainBytes)
			}
			printHexPtr(f.fs, addr)
		}
		f.fs.Write(closeParenBytes)
	}

	// Display dereferenced value.
	switch {
	case nilFound:
		f.fs.Write(nilAngleBytes)

	case cycleFound:
		f.fs.Write(circularShortBytes)

	default:
		f.ignoreNextType = true
		f.format(ve)
	}
}

// format is the main workhorse for providing the Formatter interface.  It
// uses the passed reflect value to figure out what kind of object we are
// dealing with and formats it appropriately.  It is a recursive function,
// however circular data structures are detected and handled properly.
func (f *formatState) format(v reflect.Value) {
	// Handle invalid reflect values immediately.
	kind := v.Kind()
	if kind == reflect.Invalid {
		f.fs.Write(invalidAngleBytes)
		return
	}

	// Handle pointers specially.
	if kind == reflect.Ptr {
		f.formatPtr(v)
		return
	}

	// Print type information unless already handled elsewhere.
	if !f.ignoreNextType && f.fs.Flag('#') {
		f.fs.Write(openParenBytes)
		f.fs.Write([]byte(v.Type().String()))
		f.fs.Write(closeParenBytes)
	}
	f.ignoreNextType = false

	// Call Stringer/error interfaces if they exist and the handle methods
	// flag is enabled.
	if !f.cs.DisableMethods {
		if (kind != reflect.Invalid) && (kind != reflect.Interface) {
			if handled := handleMethods(f.cs, f.fs, v); handled {
				return
			}
		}
	}

	switch kind {
	case reflect.Invalid:
		// Do nothing.  We should never get here since invalid has already
		// been handled above.

	case reflect.Bool:
		printBool(f.fs, v.Bool())

	case reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64, reflect.Int:
		printInt(f.fs, v.Int(), 10)

	case reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uint:
		printUint(f.fs, v.Uint(), 10)

	case reflect.Float32:
		printFloat(f.fs, v.Float(), 32)

	case reflect.Float64:
		printFloat(f.fs, v.Float(), 64)

	case reflect.Complex64:
		printComplex(f.fs, v.Complex(), 32)

	case reflect.Complex128:
		printComplex(f.fs, v.Complex(), 64)

	case reflect.Slice:
		if v.IsNil() {
			f.fs.Write(nilAngleBytes)
			break
		}
		fallthrough

	case reflect.Array:
		f.fs.Write(openBracketBytes)
		f.depth++
		if (f.cs.MaxDepth != 0) && (f.depth > f.cs.MaxDepth) {
			f.fs.Write(maxShortBytes)
		} else {
			numEntries := v.Len()
			for i := 0; i < numEntries; i++ {
				if i > 0 {
					f.fs.Write(spaceBytes)
				}
				f.ignoreNextType = true
				f.format(f.unpackValue(v.Index(i)))
			}
		}
		f.depth--
		f.fs.Write(closeBracketBytes)

	case reflect.String:
		f.fs.Write([]byte(v.String()))

	case reflect.Interface:
		// The only time we should get here is for nil interfaces due to
		// unpackValue calls.
		if v.IsNil() {
			f.fs.Write(nilAngleBytes)
		}

	case reflect.Ptr:
		// Do nothing.  We should never get here since pointers have already
		// been handled above.

	case reflect.Map:
		// nil maps should be indicated as different than empty maps
		if v.IsNil() {
			f.fs.Write(nilAngleBytes)
			break
		}

		f.fs.Write(openMapBytes)
		f.depth++
		if (f.cs.MaxDepth != 0) && (f.depth > f.cs.MaxDepth) {
			f.fs.Write(maxShortBytes)
		} else {
			keys := v.MapKeys()
			if f.cs.SortKeys {
				sortValues(keys, f.cs)
			}
			for i, key := range keys {
				if i > 0 {
					f.fs.Write(spaceBytes)
				}
				f.ignoreNextType = true
				f.format(f.unpackValue(key))
				f.fs.Write(colonBytes)
				f.ignoreNextType = true
				f.format(f.unpackValue(v.MapIndex(key)))
			}
		}
		f.depth--
		f.fs.Write(closeMapBytes)

	case reflect.Struct:
		numFields := v.NumField()
		f.fs.Write(openBraceBytes)
		f.depth++
		if (f.cs.MaxDepth != 0) && (f.depth > f.cs.MaxDepth) {
			f.fs.Write(maxShortBytes)
		} else {
			vt := v.Type()
			for i := 0; i < numFields; i++ {
				if i > 0 {
					f.fs.Write(spaceBytes)
				}
				vtf := vt.Field(i)
				if f.fs.Flag('+') || f.fs.Flag('#') {
					f.fs.Write([]byte(vtf.Name))
					f.fs.Write(colonBytes)
				}
				f.format(f.unpackValue(v.Field(i)))
			}
		}
		f.depth--
		f.fs.Write(closeBraceBytes)

	case reflect.Uintptr:
		printHexPtr(f.fs, uintptr(v.Uint()))

	case reflect.UnsafePointer, reflect.Chan, reflect.Func:
		printHexPtr(f.fs, v.Pointer())

	// There were not any other types at the time this code was written, but
	// fall back to letting the default fmt package handle it if any get added.
	default:
		format := f.buildDefaultFormat()
		if v.CanInterface() {
			fmt.Fprintf(f.fs, format, v.Interface())
		} else {
			fmt.Fprintf(f.fs, format, v.String())
		}
	}
}

// Format satisfies the fmt.Formatter interface. See NewFormatter for usage
// details.
func (f *formatState) Format(fs fmt.State, verb rune) {
	f.fs = fs

	// Use standard formatting for verbs that are not v.
	if verb != 'v' {
		format := f.constructOrigFormat(verb)
		fmt.Fprintf(fs, format, f.value)
		return
	}

	if f.value == nil {
		if fs.Flag('#') {
			fs.Write(interfaceBytes)
		}
		fs.Write(nilAngleBytes)
		return
	}

	f.format(reflect.ValueOf(f.value))
}

// newFormatter is a helper function to consolidate the logic from the various
// public methods which take varying config states.
func newFormatter(cs *ConfigState, v interface{}) fmt.Formatter {
	fs := &formatState{value: v, cs: cs}
	fs.pointers = make(map[uintptr]int)
	return fs
}

/*
NewFormatter returns a custom formatter that satisfies the fmt.Formatter
interface.  As a result, it integrates cleanly with standard fmt package
printing functions.  The formatter is useful for inline printing of smaller data
types similar to the standard %v format specifier.

The custom formatter only responds to the %v (most compact), %+v (adds pointer
addresses), %#v (adds types), or %#+v (adds types and pointer addresses) verb
combinations.  Any other verbs such as %x and %q will be sent to the the
standard fmt package for formatting.  In addition, the custom formatter ignores
the width and precision arguments (however they will still work on the format
specifiers not handled by the custom formatter).

Typically this function shouldn't be called directly.  It is much easier to make
use of the custom formatter by calling one of the convenience functions such as
Printf, Println, or Fprintf.
*/
func NewFormatter(v interface{}) fmt.Formatter {
	return newFormatter(&Config, v)
}



// Errorf is a wrapper for fmt.Errorf that treats each argument as if it were
// passed with a default Formatter interface returned by NewFormatter.  It
// returns the formatted string as a value that satisfies error.  See
// NewFormatter for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Errorf(format, spew.NewFormatter(a), spew.NewFormatter(b))
func Errorf(format string, a ...interface{}) (err error) {
	return fmt.Errorf(format, convertArgs(a)...)
}

// Fprint is a wrapper for fmt.Fprint that treats each argument as if it were
// passed with a default Formatter interface returned by NewFormatter.  It
// returns the number of bytes written and any write error encountered.  See
// NewFormatter for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Fprint(w, spew.NewFormatter(a), spew.NewFormatter(b))
func Fprint(w io.Writer, a ...interface{}) (n int, err error) {
	return fmt.Fprint(w, convertArgs(a)...)
}

// Fprintf is a wrapper for fmt.Fprintf that treats each argument as if it were
// passed with a default Formatter interface returned by NewFormatter.  It
// returns the number of bytes written and any write error encountered.  See
// NewFormatter for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Fprintf(w, format, spew.NewFormatter(a), spew.NewFormatter(b))
func Fprintf(w io.Writer, format string, a ...interface{}) (n int, err error) {
	return fmt.Fprintf(w, format, convertArgs(a)...)
}

// Fprintln is a wrapper for fmt.Fprintln that treats each argument as if it
// passed with a default Formatter interface returned by NewFormatter.  See
// NewFormatter for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Fprintln(w, spew.NewFormatter(a), spew.NewFormatter(b))
func Fprintln(w io.Writer, a ...interface{}) (n int, err error) {
	return fmt.Fprintln(w, convertArgs(a)...)
}

// Print is a wrapper for fmt.Print that treats each argument as if it were
// passed with a default Formatter interface returned by NewFormatter.  It
// returns the number of bytes written and any write error encountered.  See
// NewFormatter for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Print(spew.NewFormatter(a), spew.NewFormatter(b))
func Print(a ...interface{}) (n int, err error) {
	return fmt.Print(convertArgs(a)...)
}

// Printf is a wrapper for fmt.Printf that treats each argument as if it were
// passed with a default Formatter interface returned by NewFormatter.  It
// returns the number of bytes written and any write error encountered.  See
// NewFormatter for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Printf(format, spew.NewFormatter(a), spew.NewFormatter(b))
func Printf(format string, a ...interface{}) (n int, err error) {
	return fmt.Printf(format, convertArgs(a)...)
}

// Println is a wrapper for fmt.Println that treats each argument as if it were
// passed with a default Formatter interface returned by NewFormatter.  It
// returns the number of bytes written and any write error encountered.  See
// NewFormatter for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Println(spew.NewFormatter(a), spew.NewFormatter(b))
func Println(a ...interface{}) (n int, err error) {
	return fmt.Println(convertArgs(a)...)
}

// Sprint is a wrapper for fmt.Sprint that treats each argument as if it were
// passed with a default Formatter interface returned by NewFormatter.  It
// returns the resulting string.  See NewFormatter for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Sprint(spew.NewFormatter(a), spew.NewFormatter(b))
func Sprint(a ...interface{}) string {
	return fmt.Sprint(convertArgs(a)...)
}

// Sprintf is a wrapper for fmt.Sprintf that treats each argument as if it were
// passed with a default Formatter interface returned by NewFormatter.  It
// returns the resulting string.  See NewFormatter for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Sprintf(format, spew.NewFormatter(a), spew.NewFormatter(b))
func Sprintf(format string, a ...interface{}) string {
	return fmt.Sprintf(format, convertArgs(a)...)
}

// Sprintln is a wrapper for fmt.Sprintln that treats each argument as if it
// were passed with a default Formatter interface returned by NewFormatter.  It
// returns the resulting string.  See NewFormatter for formatting details.
//
// This function is shorthand for the following syntax:
//
//	fmt.Sprintln(spew.NewFormatter(a), spew.NewFormatter(b))
func Sprintln(a ...interface{}) string {
	return fmt.Sprintln(convertArgs(a)...)
}

// convertArgs accepts a slice of arguments and returns a slice of the same
// length with each argument converted to a default spew Formatter interface.
func convertArgs(args []interface{}) (formatters []interface{}) {
	formatters = make([]interface{}, len(args))
	for index, arg := range args {
		formatters[index] = NewFormatter(arg)
	}
	return formatters
}
