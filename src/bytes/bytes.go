// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package bytes implements functions for the manipulation of byte slices.
// It is analogous to the facilities of the strings package.
package bytes

//+gobra

import (
	// @	. "verification/utils/definitions"
	// @	sl "gobra-libs/byteslice"
	// @	b "verification/utils/bitwise"
	// @	rsl "verification/utils/slices"
	// #	seqs "gobra-libs/seqs"
	// #	sets "gobra-libs/sets"
	// @	. "bytes/spec"
	"internal/bytealg"
	"unicode"
	"unicode/utf8"
)

// Equal reports whether a and b
// are the same length and contain the same bytes.
// A nil argument is equivalent to an empty slice.
//
// @ preserves acc(sl.Bytes(a, 0, len(a)), R41)
//
// @ preserves acc(sl.Bytes(b, 0, len(b)), R41)
//
// @ ensures res == ( View(a) == View(b) )
//
// @ decreases
func Equal(a, b []byte) (res bool) {
	// Neither cmd/compile nor gccgo allocates for these string conversions.
	//gobra:rewrite bb601b0360eb4c70921af43549f6965f5b00ec78f7f6b39abd84a83639cd2a48
	//gobra:cont 	return string(a) == string(b)
	//gobra:end-old-code bb601b0360eb4c70921af43549f6965f5b00ec78f7f6b39abd84a83639cd2a48
	ret := /* @ unfolding acc(sl.Bytes(a, 0, len(a)), R41) in @ */ string(a) == /* @ unfolding acc(sl.Bytes(b, 0, len(b)), R41) in @ */ string(b)
	// @ stringEqualsImplViewEquals(ret, a, b, R41)
	return ret
	//gobra:endrewrite bb601b0360eb4c70921af43549f6965f5b00ec78f7f6b39abd84a83639cd2a48
}

// Compare returns an integer comparing two byte slices lexicographically.
// The result will be 0 if a == b, -1 if a < b, and +1 if a > b.
// A nil argument is equivalent to an empty slice.
// @ preserves acc(sl.Bytes(a, 0, len(a)), R40)
//
// @ preserves acc(sl.Bytes(b, 0, len(b)), R40)
//
// @ decreases
func Compare(a, b []byte) int {
	return bytealg.Compare(a, b)
}

// explode splits s into a slice of UTF-8 sequences, one per Unicode code point (still slices of bytes),
// up to a maximum of n byte slices. Invalid UTF-8 sequences are chopped into individual bytes.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ ensures forall i int :: {&res[i]} 0 <= i && i < len(res) ==> acc(&res[i])
// @ trusted // TODO
//
// @ decreases
func explode(s []byte, n int) (res [][]byte) {
	if n <= 0 || n > len(s) {
		n = len(s)
	}
	a := make([][]byte, n)
	var size int
	na := 0
	for len(s) > 0 {
		if na+1 >= n {
			a[na] = s
			na++
			break
		}
		_, size = utf8.DecodeRune(s)
		a[na] = s[0:size:size]
		s = s[size:]
		na++
	}
	return a[0:na]
}

// Count counts the number of non-overlapping instances of sep in s.
// If sep is an empty slice, Count returns 1 + the number of UTF-8-encoded code points in s.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R39)
//
// @ preserves acc(sl.Bytes(sep, 0, len(sep)), R39)
//
// @ ensures res >= 0
//
// @ ensures len(indices) == res
//
// @ ensures len(sep) > 0  ==> forall i int :: { i in indices } (i in indices) ==> ( InRangeInc(i, 0, len(s) - len(sep)) && SubviewEq(View(s), View(sep), i) )
//
// @ ensures len(sep) > 0  ==> forall i, j int  :: { i in indices, j in indices }  (i in indices) && (j in indices) && i != j ==> (i + len(sep) <= j) || (j + len(sep) <= i)
//
// @ ensures len(sep) > 0  ==> forall i int :: { i in indices } !(i in indices) ==> ( !InRangeInc(i, 0, len(s) - len(sep)) || View(s)[i:i+len(sep)] != View(sep) || SetContainsInRange(indices, i-len(sep), i))
//
// @ ensures len(sep) == 0 ==> forall i int :: {i in indices} i in indices ==> 0 <= i && i <= len(s)
//
// @ decreases
func Count(s, sep []byte) (res int /* @ , ghost indices set[int] @ */) {
	// special case
	if len(sep) == 0 {
		//gobra:rewrite 3c341f4b0a84096a6659ee1fdfb4602bd26f52827793010c440fd0c659976395
		//gobra:cont 		return unicode_utf8__RuneCount(s) + 1
		//gobra:end-old-code 3c341f4b0a84096a6659ee1fdfb4602bd26f52827793010c440fd0c659976395
		res /* @ , indices @ */ = utf8.RuneCount(s)
		return res + 1 // @ , indices union set[int]{len(s)}
		//gobra:endrewrite 3c341f4b0a84096a6659ee1fdfb4602bd26f52827793010c440fd0c659976395
	}
	if len(sep) == 1 {
		//gobra:rewrite 66239cff85d3bf25c4daa1d173a4c87733b57ef726a40dc7d98f63cf47ccdf38
		//gobra:cont 		return bytealg.Count(s,
		//gobra:cont 			/* @ unfolding acc(sl.Bytes(sep, 0, len(sep)), R40) in @ */ sep[0])
		//gobra:end-old-code 66239cff85d3bf25c4daa1d173a4c87733b57ef726a40dc7d98f63cf47ccdf38
		res /* @ , indices @ */ = bytealg.Count(s,
			/* @ unfolding acc(sl.Bytes(sep, 0, len(sep)), R40) in @ */ sep[0])
		// @ assert forall i int :: { View(s)[i:i+len(sep)] } 0 <= i && i < len(s) ==> View(s)[i:i+len(sep)] == seq[byte]{View(s)[i]}
		return res // @ , indices
		//gobra:endrewrite 66239cff85d3bf25c4daa1d173a4c87733b57ef726a40dc7d98f63cf47ccdf38
	}
	n := 0
	// @ ghost olds := s
	// @ ghost idx := 0
	// @ ghost indices = set[int]{}
	// @ invariant InRangeInc(idx, 0, len(olds))
	// @ invariant olds[idx:] === s
	// @ invariant n >= 0
	// @ invariant len(indices) == n
	// @ invariant forall j int :: {j in indices} j in indices ==> j < idx
	// @ invariant acc(sl.Bytes(olds, 0, len(olds)), R39)
	// @ invariant acc(sl.Bytes(sep, 0, len(sep)), R39)
	// @ invariant forall j int :: { j in indices }{ View(olds)[j:j+len(sep)] } j in indices ==> View(olds)[j:j+len(sep)] == View(sep) && !SetContainsInRange(indices, j-len(sep), j)
	// @ invariant forall j int :: { j in indices }{ View(olds)[j:j+len(sep)] } !(j in indices) ==> !(InRangeInc(j, 0, idx - len(sep))) || View(olds)[j:j+len(sep)] != View(sep) || SetContainsInRange(indices, j-len(sep), j)
	// @ invariant forall j int :: { j in indices } j in indices ==> InRange(j, 0, idx-len(sep))
	// @ invariant forall j int :: { j in indices } j in indices ==> InRange(j, 0, len(olds) - len(sep))
	// @ invariant forall i, j int  :: { i in indices, j in indices }  (i in indices) && (j in indices) && i != j ==> (i + len(sep) < j) || (j + len(sep) < i)
	// @ decreases len(s)
	for {
		// @ ghost p := R39 - R40 / 2
		// @ unfold acc(sl.Bytes(olds, 0, len(olds)), p)

		// @ assert forall j int :: {&olds[idx:][j]} 0 <= j && j < len(olds[idx:]) ==> &olds[idx:][j] == &olds[j+idx]

		// @ fold acc(sl.Bytes(olds, 0, len(olds)), p)
		// @ unfold acc(sl.Bytes(olds, 0, len(olds)), p)

		// @ fold acc(sl.Bytes(s, 0, len(s)), p)
		i := Index(s, sep)
		// @ ghost vs := View(s)
		// @ unfold acc(sl.Bytes(s, 0, len(s)), p)

		// @ fold acc(sl.Bytes(olds, 0, len(olds)), p)
		// @ assert vs == View(olds)[idx:]
		if i == -1 {

			// @ ghost vs := View(olds)
			// @ ghost vsep := View(sep)

			// @ lemmaCountAux(View(olds), View(sep), indices, idx)

			return n // @ , indices
		}

		// @ unfold acc(sl.Bytes(olds, 0, len(olds)), R39)

		// @ unfold acc(sl.Bytes(sep, 0, len(sep)), R39)

		// @ fold acc(sl.Bytes(sep, 0, len(sep)), R39)
		// @ fold acc(sl.Bytes(olds, 0, len(olds)), R39)

		// @ assert InRangeInc(i, 0, len(s) - len(sep))
		// @ assert len(s) + idx == len(olds)
		// @ assert InRangeInc(idx+i, idx, len(olds) - len(sep))
		// @ assert InRangeInc(idx+i, 0, len(olds) - len(sep))

		// @ unfold acc(sl.Bytes(olds, 0, len(olds)), R39)
		// @ unfold acc(sl.Bytes(sep, 0, len(sep)), R39)

		// @ indices = indices union set[int]{idx+i}
		// TODO: I dont understand why this doesn't hold
		// @ assume forall i, j int  :: { i in indices, j in indices }  (i in indices) && (j in indices) ==> (i + len(sep) < j) || (j + len(sep) < i)

		n++
		s = s[i+len(sep):]

		// @ idx += i + len(sep)

		// @ fold acc(sl.Bytes(olds, 0, len(olds)), R39)
		// @ fold acc(sl.Bytes(sep, 0, len(sep)), R39)
	}
}

// Contains reports whether subslice is within b.
//
// @ preserves acc(sl.Bytes(b, 0, len(b)), R40)
//
// @ preserves acc(sl.Bytes(subslice, 0, len(subslice)), R40)
//
// @ ensures res == ( exists i int :: { View(b)[i:i+len(subslice)] } 0 <= i && i + len(subslice) <= len(b) && View(b)[i:i+len(subslice)] == View(subslice) )
//
// @ decreases
func Contains(b, subslice []byte) (res bool) {
	return Index(b, subslice) != -1
}

// ContainsAny reports whether any of the UTF-8-encoded code points in chars are within b.
// @ trusted
func ContainsAny(b []byte, chars string) bool {
	return IndexAny(b, chars) >= 0
}

// ContainsRune reports whether the rune is contained in the UTF-8-encoded byte slice b.
// @ trusted
func ContainsRune(b []byte, r rune) bool {
	return IndexRune(b, r) >= 0
}

// IndexByte returns the index of the first instance of c in b, or -1 if c is not present in b.
//
// @ preserves acc(sl.Bytes(b, 0, len(b)), R45)
//
// @ ensures -1 <= res && res < len(b)
//
// @ ensures res != -1 ==> ((forall i int :: {View(b)[i]} 0 <= i && i < res ==> View(b)[i] != c) && View(b)[res] == c)
//
// @ ensures res == -1 == (forall i int :: {View(b)[i]} 0 <= i && i < len(b) ==> View(b)[i] != c)
//
// @ decreases
func IndexByte(b []byte, c byte) (res int) {
	return bytealg.IndexByte(b, c)
}

// @ preserves forall i int :: {&s[i]} 0 <= i && i < len(s) ==> acc(&s[i], R40)
//
// @ preserves acc(s, R40)
//
// @ decreases
func indexBytePortable(s []byte, c byte) int {
	// @ invariant forall j int :: {&s[j]} 0 <= j && j < len(s) ==> acc(&s[j], R40)
	// @ invariant acc(s, R40)
	// @ decreases len(s) - i0
	for i, b := range s /* @ with i0 @ */ {
		if b == c {
			return i
		}
	}
	return -1
}

// LastIndex returns the index of the last instance of sep in s, or -1 if sep is not present in s.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ preserves acc(sl.Bytes(sep, 0, len(sep)), R40)
//
// @ decreases
func LastIndex(s, sep []byte) int {
	n := len(sep)
	switch {
	case n == 0:
		return len(s)
	case n == 1:
		return LastIndexByte(s,
			/* @ unfolding acc(sl.Bytes(sep, 0, len(sep)), R40) in @ */ sep[0])
	case n == len(s):
		if Equal(s, sep) {
			return 0
		}
		return -1
	case n > len(s):
		return -1
	}
	// Rabin-Karp search from the end of the string
	hashss, pow := bytealg.HashStrRevBytes(sep)
	last := len(s) - n
	var h uint32

	// @ invariant acc(sl.Bytes(s, 0, len(s)), R40)
	// @ invariant i < len(s)
	// @ invariant i - last >= -1
	// @ decreases i - last
	for i := len(s) - 1; i >= last; i-- {
		// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
		h = h*bytealg.PrimeRK + uint32(s[i])
		// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
	}
	// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
	// @ assert forall i int :: {&s[last:][i]} 0 <= i && i < len(s[last:]) ==> &s[last:][i] == &s[i+last]
	// @ fold acc(sl.Bytes(s[last:], 0, len(s[last:])), R40)
	if h == hashss && Equal(s[last:], sep) {
		// @ unfold acc(sl.Bytes(s[last:], 0, len(s[last:])), R40)
		// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
		return last
	}
	// @ unfold acc(sl.Bytes(s[last:], 0, len(s[last:])), R40)
	// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
	// @ invariant acc(sl.Bytes(s, 0, len(s)), R40)
	// @ invariant acc(sl.Bytes(sep, 0, len(sep)), R40)
	// @ invariant i < last && last < len(s)
	// @ invariant i >= -1
	// @ decreases i
	for i := last - 1; i >= 0; i-- {
		// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)

		h *= bytealg.PrimeRK
		h += uint32(s[i])
		h -= pow * uint32(s[i+n])
		// @ assert forall j int :: {&s[i:i+n][j]} 0 <= j && j < len(s[i:i+n]) ==> &s[i:i+n][j] == &s[j+i]
		// @ fold acc(sl.Bytes(s[i:i+n], 0, len(s[i:i+n])), R40)
		if h == hashss && Equal(s[i:i+n], sep) {
			// @ unfold acc(sl.Bytes(s[i:i+n], 0, len(s[i:i+n])), R40)
			// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
			return i
		}
		// @ unfold acc(sl.Bytes(s[i:i+n], 0, len(s[i:i+n])), R40)
		// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
	}
	return -1
}

// LastIndexByte returns the index of the last instance of c in s, or -1 if c is not present in s.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ decreases
func LastIndexByte(s []byte, c byte) int {
	// @ invariant i < len(s)
	// @ invariant acc(sl.Bytes(s, 0, len(s)), R40)
	// @ decreases i
	for i := len(s) - 1; i >= 0; i-- {
		// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
		if s[i] == c {
			// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
			return i
		}
		// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
	}
	return -1
}

// IndexRune interprets s as a sequence of UTF-8-encoded code points.
// It returns the byte index of the first occurrence in s of the given rune.
// It returns -1 if rune is not present in s.
// If r is utf8.RuneError, it returns the first instance of any
// invalid UTF-8 byte sequence.
//
// @ requires acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ decreases
func IndexRune(s []byte, r rune) int {
	switch {
	case 0 <= r && r < utf8.RuneSelf:
		return IndexByte(s, byte(r))
	case r == utf8.RuneError:
		// @ invariant acc(sl.Bytes(s, 0, len(s)), R40)
		// @ invariant i >= 0
		// @ decreases len(s) - i
		for i := 0; i < len(s); {
			// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
			// @ assert forall j int :: {&s[i:][j]} 0 <= j && j < len(s[i:]) ==> &s[i:][j] == &s[j+i]
			// @ fold acc(sl.Bytes(s[i:], 0, len(s[i:])), R40)
			r1, n := utf8.DecodeRune(s[i:])
			// @ unfold acc(sl.Bytes(s[i:], 0, len(s[i:])), R40)
			// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
			if r1 == utf8.RuneError {
				return i
			}
			i += n
		}
		return -1
	case !utf8.ValidRune(r):
		return -1
	default:
		var b /* @ @ @ */ [utf8.UTFMax]byte
		n := utf8.EncodeRune(b[:], r)
		// @ fold sl.Bytes(b[:n], 0, len(b[:n]))
		return Index(s, b[:n])
	}
}

// IndexAny interprets s as a sequence of UTF-8-encoded Unicode code points.
// It returns the byte index of the first occurrence in s of any of the Unicode
// code points in chars. It returns -1 if chars is empty or if there is no code
// point in common.
// @ trusted
func IndexAny(s []byte, chars string) int {
	if chars == "" {
		// Avoid scanning all of s.
		return -1
	}
	if len(s) == 1 {
		r := rune(s[0])
		if r >= utf8.RuneSelf {
			// search utf8.RuneError.
			for _, r = range chars {
				if r == utf8.RuneError {
					return 0
				}
			}
			return -1
		}
		if bytealg.IndexByteString(chars, s[0]) >= 0 {
			return 0
		}
		return -1
	}
	if len(chars) == 1 {
		r := rune(chars[0])
		if r >= utf8.RuneSelf {
			r = utf8.RuneError
		}
		return IndexRune(s, r)
	}
	if len(s) > 8 {
		//gobra:rewrite 79bb992678a3529157ae695b69ecaa3de653abaad4acbe514ff06663afdea383
		//gobra:cont 		if as, isASCII := makeASCIISet(chars); isASCII {
		//gobra:cont 			for i, c := range s {
		//gobra:cont 				if as.contains(c) {
		//gobra:end-old-code 79bb992678a3529157ae695b69ecaa3de653abaad4acbe514ff06663afdea383
		if asc, isASCII := makeASCIISet(chars); isASCII {
			for i, c := range s {
				if asc.contains(c) {
					//gobra:endrewrite 79bb992678a3529157ae695b69ecaa3de653abaad4acbe514ff06663afdea383
					return i
				}
			}
			return -1
		}
	}
	var width int
	for i := 0; i < len(s); i += width {
		r := rune(s[i])
		if r < utf8.RuneSelf {
			if bytealg.IndexByteString(chars, s[i]) >= 0 {
				return i
			}
			width = 1
			continue
		}
		r, width = utf8.DecodeRune(s[i:])
		if r != utf8.RuneError {
			// r is 2 to 4 bytes
			if len(chars) == width {
				if chars == string(r) {
					return i
				}
				continue
			}
			// Use bytealg.IndexString for performance if available.
			if bytealg.MaxLen >= width {
				if bytealg.IndexString(chars, string(r)) >= 0 {
					return i
				}
				continue
			}
		}
		for _, ch := range chars {
			if r == ch {
				return i
			}
		}
	}
	return -1
}

// LastIndexAny interprets s as a sequence of UTF-8-encoded Unicode code
// points. It returns the byte index of the last occurrence in s of any of
// the Unicode code points in chars. It returns -1 if chars is empty or if
// there is no code point in common.
// @ trusted
func LastIndexAny(s []byte, chars string) int {
	if chars == "" {
		// Avoid scanning all of s.
		return -1
	}
	if len(s) > 8 {
		//gobra:end-old-code e49149cc4c895a7bc244c9b14ef42c0429e517ba21ea01addfcd584a63a08e54
		if asc, isASCII := makeASCIISet(chars); isASCII {
			for i := len(s) - 1; i >= 0; i-- {
				if asc.contains(s[i]) {
					//gobra:endrewrite e49149cc4c895a7bc244c9b14ef42c0429e517ba21ea01addfcd584a63a08e54
					return i
				}
			}
			return -1
		}
	}
	if len(s) == 1 {
		r := rune(s[0])
		if r >= utf8.RuneSelf {
			for _, r = range chars {
				if r == utf8.RuneError {
					return 0
				}
			}
			return -1
		}
		if bytealg.IndexByteString(chars, s[0]) >= 0 {
			return 0
		}
		return -1
	}
	if len(chars) == 1 {
		cr := rune(chars[0])
		if cr >= utf8.RuneSelf {
			cr = utf8.RuneError
		}
		for i := len(s); i > 0; {
			r, size := utf8.DecodeLastRune(s[:i])
			i -= size
			if r == cr {
				return i
			}
		}
		return -1
	}
	for i := len(s); i > 0; {
		r := rune(s[i-1])
		if r < utf8.RuneSelf {
			if bytealg.IndexByteString(chars, s[i-1]) >= 0 {
				return i - 1
			}
			i--
			continue
		}
		r, size := utf8.DecodeLastRune(s[:i])
		i -= size
		if r != utf8.RuneError {
			// r is 2 to 4 bytes
			if len(chars) == size {
				if chars == string(r) {
					return i
				}
				continue
			}
			// Use bytealg.IndexString for performance if available.
			if bytealg.MaxLen >= size {
				if bytealg.IndexString(chars, string(r)) >= 0 {
					return i
				}
				continue
			}
		}
		for _, ch := range chars {
			if r == ch {
				return i
			}
		}
	}
	return -1
}

// Generic split: splits after each instance of sep,
// including sepSave bytes of sep in the subslices.
//
// @ trusted // TODO
func genSplit(s, sep []byte, sepSave, n int) [][]byte {
	if n == 0 {
		return nil
	}
	if len(sep) == 0 {
		return explode(s, n)
	}
	if n < 0 {
		//gobra:rewrite 3165d2315c1f2510a7dffaae76bc9952201ebfb9afaa952a59aa03ab052ec8c5
		//gobra:cont 		n = Count(s, sep) + 1
		//gobra:end-old-code 3165d2315c1f2510a7dffaae76bc9952201ebfb9afaa952a59aa03ab052ec8c5
		n1 /*@, idxs @*/ := Count(s, sep)
		n = n1 + 1
		//gobra:endrewrite 3165d2315c1f2510a7dffaae76bc9952201ebfb9afaa952a59aa03ab052ec8c5
	}
	if n > len(s)+1 {
		n = len(s) + 1
	}

	a := make([][]byte, n)
	n--
	i := 0
	for i < n {
		m := Index(s, sep)
		if m < 0 {
			break
		}
		a[i] = s[: m+sepSave : m+sepSave]
		s = s[m+len(sep):]
		i++
	}
	a[i] = s
	return a[:i+1]
}

// SplitN slices s into subslices separated by sep and returns a slice of
// the subslices between those separators.
// If sep is empty, SplitN splits after each UTF-8 sequence.
// The count determines the number of subslices to return:
//
//	n > 0: at most n subslices; the last subslice will be the unsplit remainder.
//	n == 0: the result is nil (zero subslices)
//	n < 0: all subslices
//
// To split around the first instance of a separator, see Cut.
//
// @ preserves acc(sl.Bytes(sep, 0, len(sep)), R39)
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R39)
// @ trusted // TODO
func SplitN(s, sep []byte, n int) [][]byte { return genSplit(s, sep, 0, n) }

// SplitAfterN slices s into subslices after each instance of sep and
// returns a slice of those subslices.
// If sep is empty, SplitAfterN splits after each UTF-8 sequence.
// The count determines the number of subslices to return:
//
//	n > 0: at most n subslices; the last subslice will be the unsplit remainder.
//	n == 0: the result is nil (zero subslices)
//	n < 0: all subslices
//
// @ trusted // TODO
func SplitAfterN(s, sep []byte, n int) [][]byte {
	return genSplit(s, sep, len(sep), n)
}

// Split slices s into all subslices separated by sep and returns a slice of
// the subslices between those separators.
// If sep is empty, Split splits after each UTF-8 sequence.
// It is equivalent to SplitN with a count of -1.
//
// To split around the first instance of a separator, see Cut.
// @ trusted // TODO
func Split(s, sep []byte) [][]byte { return genSplit(s, sep, 0, -1) }

// SplitAfter slices s into all subslices after each instance of sep and
// returns a slice of those subslices.
// If sep is empty, SplitAfter splits after each UTF-8 sequence.
// It is equivalent to SplitAfterN with a count of -1.
// @ trusted // TODO
func SplitAfter(s, sep []byte) [][]byte {
	return genSplit(s, sep, len(sep), -1)
}

// gobra incorrectly rejects \v. see issue #782
//
//gobra:rewrite d7c610dc5fc5a8d07a0fc96646bdef7e515c72b766cd6916911b7c09642ca60c
//gobra:cont var asciiSpace = [256]uint8{'\t': 1, '\n': 1, '\v': 1, '\f': 1, '\r': 1, ' ': 1}
//gobra:end-old-code d7c610dc5fc5a8d07a0fc96646bdef7e515c72b766cd6916911b7c09642ca60c
var asciiSpace = [256]uint8{'\t': 1, '\n': 1, '\f': 1, '\r': 1, ' ': 1}

//gobra:endrewrite d7c610dc5fc5a8d07a0fc96646bdef7e515c72b766cd6916911b7c09642ca60c

// Fields interprets s as a sequence of UTF-8-encoded code points.
// It splits the slice s around each instance of one or more consecutive white space
// characters, as defined by unicode.IsSpace, returning a slice of subslices of s or an
// empty slice if s contains only white space.
//
// @ requires forall i int :: {asciiSpace[i]} 0 <= i && i < len(asciiSpace) ==> asciiSpace[i] == 0 || asciiSpace[i] == 1
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
// @ trusted
func Fields(s []byte) [][]byte {
	// First count the fields.
	// This is an exact count if s is ASCII, otherwise it is an approximation.
	n := 0
	wasSpace := 1
	// setBits is used to track which bits are set in the bytes of s.
	setBits := uint8(0)
	// @ invariant i >= 0
	// @ invariant acc(sl.Bytes(s, 0, len(s)), R40)
	// @ invariant forall i int :: {asciiSpace[i]} 0 <= i && i < len(asciiSpace) ==> asciiSpace[i] == 0 || asciiSpace[i] == 1
	// @ invariant wasSpace == 0 || wasSpace == 1
	// @ invariant n >= 0
	for i := 0; i < len(s); i++ {
		// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
		r := s[i]
		// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
		// @ b.ByteValue(r)
		//gobra:rewrite 22b50ee41a8e778fc5ba05e0b251e268cb4ea75db756138a2077c79b65c6068b
		//gobra:cont 		setBits |= r
		//gobra:end-old-code 22b50ee41a8e778fc5ba05e0b251e268cb4ea75db756138a2077c79b65c6068b
		setBits |= uint8(r)
		//gobra:endrewrite 22b50ee41a8e778fc5ba05e0b251e268cb4ea75db756138a2077c79b65c6068b
		isSpace := int(asciiSpace[r])
		n += wasSpace & ^isSpace
		wasSpace = isSpace
	}

	if setBits >= utf8.RuneSelf {
		// Some runes in the input slice are not ASCII.
		return FieldsFunc(s, unicode.IsSpace)
	}

	// ASCII fast path
	a := make([][]byte, n)
	na := 0
	fieldStart := 0
	i := 0
	// Skip spaces in the front of the input.
	//gobra:rewrite 2b01f87ca5f267ff7eac5cae2fb4faa34f996f6ebcbbf22f4d67a3cd3a3d0cf5
	//gobra:cont 	for i < len(s) && asciiSpace[s[i]] != 0 {
	//gobra:cont 		i++
	//gobra:cont 	}
	//gobra:end-old-code 2b01f87ca5f267ff7eac5cae2fb4faa34f996f6ebcbbf22f4d67a3cd3a3d0cf5
	// @ invariant acc(sl.Bytes(s, 0, len(s)), R40)
	// @ invariant 0 <= i && i <= len(s)
	for {
		// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
		if !(i < len(s)) {
			// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
			break
		}
		// @ b.ByteValue(s[i])
		if !(asciiSpace[s[i]] != 0) {
			// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
			break
		}
		// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
		i++
	}
	//gobra:endrewrite 2b01f87ca5f267ff7eac5cae2fb4faa34f996f6ebcbbf22f4d67a3cd3a3d0cf5
	fieldStart = i
	// @ invariant acc(sl.Bytes(s, 0, len(s)), R40)
	// @ invariant 0 <= i && i <= len(s)
	// @ invariant 0 <= fieldStart && fieldStart <= i
	// @ invariant forall j int :: {&a[j]} 0 <= j && j < len(a) ==> acc(&a[j])
	// @ invariant 0 <= na
	for i < len(s) {
		// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
		// @ b.ByteValue(s[i])
		if asciiSpace[s[i]] == 0 {
			i++
			// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
			continue
		}
		a[na] = s[fieldStart:i:i]
		na++
		i++
		// Skip spaces in between fields.
		for i < len(s) && asciiSpace[s[i]] != 0 {
			i++
		}
		fieldStart = i
		// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
	}
	if fieldStart < len(s) { // Last field might end at EOF.
		a[na] = s[fieldStart:len(s):len(s)]
	}
	return a
}

// FieldsFunc interprets s as a sequence of UTF-8-encoded code points.
// It splits the slice s at each run of code points c satisfying f(c) and
// returns a slice of subslices of s. If all code points in s satisfy f(c), or
// len(s) == 0, an empty slice is returned.
//
// FieldsFunc makes no guarantees about the order in which it calls f(c)
// and assumes that f always returns the same value for a given c.
// @ trusted
func FieldsFunc(s []byte, f func(rune) bool) [][]byte {
	// A span is used to record a slice of s of the form s[start:end].
	// The start index is inclusive and the end index is exclusive.
	type span struct {
		start int
		end   int
	}
	spans := make([]span, 0, 32)

	// Find the field start and end indices.
	// Doing this in a separate pass (rather than slicing the string s
	// and collecting the result substrings right away) is significantly
	// more efficient, possibly due to cache effects.
	start := -1 // valid span start if >= 0
	for i := 0; i < len(s); {
		size := 1
		r := rune(s[i])
		if r >= utf8.RuneSelf {
			r, size = utf8.DecodeRune(s[i:])
		}
		if f(r) {
			if start >= 0 {
				spans = append( /*@ R50, @*/ spans, span{start, i})
				start = -1
			}
		} else {
			if start < 0 {
				start = i
			}
		}
		i += size
	}

	// Last field might end at EOF.
	if start >= 0 {
		spans = append( /* @ R50, @ */ spans, span{start, len(s)})
	}

	// Create subslices from recorded field indices.
	a := make([][]byte, len(spans))
	for i, span := range spans {
		a[i] = s[span.start:span.end:span.end]
	}

	return a
}

// Join concatenates the elements of s to create a new byte slice. The separator
// sep is placed between elements in the resulting slice.
// @ trusted // TODO
func Join(s [][]byte, sep []byte) []byte {
	if len(s) == 0 {
		return []byte{}
	}
	if len(s) == 1 {
		// Just return a copy.
		return append( /* @ R40, @ */ []byte(nil), s[0]...)
	}
	n := len(sep) * (len(s) - 1)
	for _, v := range s {
		n += len(v)
	}

	b := make([]byte, n)
	bp := copy(b, s[0] /* @, R40 @ */)
	for _, v := range s[1:] {
		bp += copy(b[bp:], sep /* @, R40 @ */)
		bp += copy(b[bp:], v /* @, R40 @ */)
	}
	return b
}

// HasPrefix tests whether the byte slice s begins with prefix.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ preserves acc(sl.Bytes(prefix, 0, len(prefix)), R40)
//
// @ ensures res ==> (len(s) >= len(prefix))
//
// @ decreases
func HasPrefix(s, prefix []byte) (res bool) {
	//gobra:rewrite 2131f6a479f4a6519ab85f42f8e546d5fb121f7ad7c941d7a6b8daf2fa33cb68
	//gobra:cont 	return len(s) >= len(prefix) && Equal(s[0:len(prefix)], prefix)
	//gobra:end-old-code 2131f6a479f4a6519ab85f42f8e546d5fb121f7ad7c941d7a6b8daf2fa33cb68
	if len(s) >= len(prefix) {
		// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
		// @ fold acc(sl.Bytes(s[0:len(prefix)], 0, len(s[0:len(prefix)])), R40)
		res = Equal(s[0:len(prefix)], prefix)
		// @ unfold acc(sl.Bytes(s[0:len(prefix)], 0, len(s[0:len(prefix)])), R40)
		// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
		return res
	}
	return false
	//gobra:endrewrite 2131f6a479f4a6519ab85f42f8e546d5fb121f7ad7c941d7a6b8daf2fa33cb68
}

// HasSuffix tests whether the byte slice s ends with suffix.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ preserves acc(sl.Bytes(suffix, 0, len(suffix)), R40)
//
// @ ensures res ==> len(s) >= len(suffix)
//
// @ decreases
func HasSuffix(s, suffix []byte) (res bool) {
	//gobra:rewrite 49653ed8abc2df0efb1fe82a8f6bccb36b7a6ca25b29b5ee7237b75d1cb8ef45
	//gobra:cont 	return len(s) >= len(suffix) && Equal(s[len(s)-len(suffix):], suffix)
	//gobra:end-old-code 49653ed8abc2df0efb1fe82a8f6bccb36b7a6ca25b29b5ee7237b75d1cb8ef45
	if len(s) >= len(suffix) {
		// @ offset := len(s) - len(suffix)
		// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
		// @ assert forall i int :: {&s[len(s)-len(suffix):][i]} 0 <= i && i < len(s[len(s)-len(suffix):]) ==> &s[len(s)-len(suffix):][i] == &s[i+len(s)-len(suffix)]
		// @ fold acc(sl.Bytes(s[len(s)-len(suffix):], 0, len(s[len(s)-len(suffix):])), R40)
		res = Equal(s[len(s)-len(suffix):], suffix)
		// @ unfold acc(sl.Bytes(s[len(s)-len(suffix):], 0, len(s[len(s)-len(suffix):])), R40)
		// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
		return res
	}
	return false
	//gobra:endrewrite 49653ed8abc2df0efb1fe82a8f6bccb36b7a6ca25b29b5ee7237b75d1cb8ef45
}

// Map returns a copy of the byte slice s with all its characters modified
// according to the mapping function. If mapping returns a negative value, the character is
// dropped from the byte slice with no replacement. The characters in s and the
// output are interpreted as UTF-8-encoded code points.
// @ trusted
// @ decreases
func Map(mapping func(r rune) rune, s []byte) []byte {
	// In the worst case, the slice can grow when mapped, making
	// things unpleasant. But it's so rare we barge in assuming it's
	// fine. It could also shrink but that falls out naturally.
	b := make([]byte, 0, len(s))
	for i := 0; i < len(s); {
		wid := 1
		r := rune(s[i])
		if r >= utf8.RuneSelf {
			r, wid = utf8.DecodeRune(s[i:])
		}
		r = mapping(r)
		if r >= 0 {
			b = utf8.AppendRune(b, r)
		}
		i += wid
	}
	return b
}

// Repeat returns a new byte slice consisting of count copies of b.
//
// It panics if count is negative or if
// the result of (len(b) * count) overflows.
//
// @ requires count >= 0
//
// @ requires count == 0 || len(b)*count/count == len(b)
//
// @ preserves acc(sl.Bytes(b, 0, len(b)), R40)
//
// @ ensures len(res) > 0 ==> sl.Bytes(res, 0, len(res))
//
// @ ensures len(res) > 0 ==> View(res) == SpecRepeat(View(b), count)
//
// @ trusted // TODO: this is extremely slow to verify sometimes
func Repeat(b []byte, count int) (res []byte) {
	if count == 0 {
		return []byte{}
	}
	// Since we cannot return an error on overflow,
	// we should panic if the repeat will generate
	// an overflow.
	// See Issue golang.org/issue/16237.
	if count < 0 {
		panic("bytes: negative Repeat count")
	} else if len(b)*count/count != len(b) {
		panic("bytes: Repeat count causes overflow")
	}

	nb := make([]byte, len(b)*count)
	// @ unfold acc(sl.Bytes(b, 0, len(b)), R41)
	bp := copy(nb, b /* @, R41 @ */)
	// @ ghost i := 1
	// @ fold acc(sl.Bytes(b, 0, len(b)), R41)
	// @ fold sl.Bytes(nb, 0, len(nb))

	// @ assert View(nb)[:bp] == View(b)
	// @ lemmaSpecRepeat_1(View(b))
	// @ assert SpecRepeat(View(b), 1) == View(b)

	// @ invariant 0 < count
	// @ invariant 0 < i
	// @ invariant bp == len(b) * i
	// @ invariant bp >= 0
	// @ invariant acc(sl.Bytes(b, 0, len(b)), R41)
	// @ invariant sl.Bytes(nb, 0, len(nb))
	// @ invariant View(nb)[:MinInt(count, i) * len(b)] == SpecRepeat(View(b), MinInt(count, i))
	for bp < len(nb) {
		// @ unfold sl.Bytes(nb, 0, len(nb))
		// @ assert 0 <= bp && bp <= len(nb)
		// @ assert bp == MinInt(count, i) * len(b)
		// @ SubSliceOverlaps(nb, bp, len(nb))
		// @ SubSliceOverlaps(nb, 0, bp)
		copy(nb[bp:], nb[:bp] /* @, R40 @ */)
		// @ fold sl.Bytes(nb, 0, len(nb))
		// @ assume View(nb)[:i * len(b)] ++ View(nb)[:i * len(b)] == View(nb)[: MinInt(count, i*2) * len(b)]
		// @ lemmaSpecRepeat_2n(View(b), i)
		// @ assert View(nb)[:i * len(b)] ++ View(nb)[:i * len(b)] == SpecRepeat(View(b), 2 * i)[: MinInt(count, i*2) * len(b)]
		// @ lemmaEqTransitive_seq(View(nb)[: MinInt(count, i*2) * len(b)], View(nb)[:i * len(b)] ++ View(nb)[:i * len(b)], View(nb)[: MinInt(count, i*2) * len(b)])
		// @ assert View(nb)[: MinInt(count, i*2) * len(b)] == SpecRepeat(View(b), 2 * i)[: MinInt(count, i*2) * len(b)]
		// @ vb := View(b)
		// @ vnb := View(nb)
		// @ assert 0 < count
		// @ assert sl.Bytes(nb, 0, len(nb))

		// @ decreases
		// @ requires acc(sl.Bytes(b, 0, len(b)), R50)
		// @ requires acc(sl.Bytes(nb, 0, len(nb)), R50)
		// @ requires 0 < count
		// @ requires 0 < i
		// @ requires View(nb)[:MinInt(count, i*2) * len(b)] == SpecRepeat(View(b), MinInt(count, i*2))
		// @ preserves 0 <= bp
		// @ preserves bp == len(b) * i
		// @ ensures 0 < count
		// @ ensures 0 < i
		// @ ensures acc(sl.Bytes(b, 0, len(b)), R50)
		// @ ensures acc(sl.Bytes(nb, 0, len(nb)), R50)
		// @ ensures View(nb)[:MinInt(count, i) * len(b)] == SpecRepeat(View(b), MinInt(count, i))
		// @ outline (
		// @ lemmaMul2Inj(bp, i, bp*2, i*2, len(b))
		bp *= 2
		// @ assert View(nb)[:MinInt(count, i*2) * len(b)] == SpecRepeat(View(b), MinInt(count, i*2))
		// @ i *= 2
		// @ assert View(nb)[:MinInt(count, i) * len(b)] == SpecRepeat(View(b), MinInt(count, i))
		// @ )
		// @ assert 0 < i
		// @ assert bp == len(b) * i
		// @ assert bp >= 0
		// @ assert sl.Bytes(nb, 0, len(nb))
		// @ assert vnb == View(nb)
		// @ assert vb == View(b)
		// @ assert View(nb)[:MinInt(count, i) * len(b)] == SpecRepeat(View(b), MinInt(count, i))
	}
	return nb
}

// ToUpper returns a copy of the byte slice s with all Unicode letters mapped to
// their upper case.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ decreases
func ToUpper(s []byte) []byte {
	isASCII, hasLower := true, false
	// @ invariant acc(sl.Bytes(s, 0, len(s)), R40)
	// @ invariant i >= 0
	// @ decreases len(s) - i
	for i := 0; i < len(s); i++ {
		// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
		c := s[i]
		// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
		if c >= utf8.RuneSelf {
			isASCII = false
			break
		}
		hasLower = hasLower || ('a' <= c && c <= 'z')
	}

	if isASCII { // optimize for ASCII-only byte slices.
		if !hasLower {
			// Just return a copy.
			//gobra:rewrite f258d575b86bb987fa4d520e7a065f05c6e6d86b6b2ac9945c067a6cf1b4cf75
			//gobra:cont 			return append( /* @ R40, @ */ []byte(""), s...)
			//gobra:end-old-code f258d575b86bb987fa4d520e7a065f05c6e6d86b6b2ac9945c067a6cf1b4cf75
			// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
			res := append( /* @ R40, @ */ []byte(""), s...)
			// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
			return res

			//gobra:endrewrite f258d575b86bb987fa4d520e7a065f05c6e6d86b6b2ac9945c067a6cf1b4cf75
		}
		b := make([]byte, len(s))
		// @ invariant acc(sl.Bytes(s, 0, len(s)), R40)
		// @ invariant forall j int :: {&b[j]} 0 <= j && j < len(b) ==> acc(&b[j], 1)
		// @ invariant i >= 0
		// @ decreases len(s) - i
		for i := 0; i < len(s); i++ {
			// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
			c := s[i]
			if 'a' <= c && c <= 'z' {
				c -= 'a' - 'A'
			}
			b[i] = c
			// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
		}
		return b
	}
	return Map(unicode.ToUpper, s)
}

// ToLower returns a copy of the byte slice s with all Unicode letters mapped to
// their lower case.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ decreases
func ToLower(s []byte) (res []byte) {
	isASCII, hasUpper := true, false
	// @ invariant acc(sl.Bytes(s, 0, len(s)), R40)
	// @ invariant i >= 0
	// @ decreases len(s) - i
	for i := 0; i < len(s); i++ {
		// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
		c := s[i]
		if c >= utf8.RuneSelf {
			isASCII = false
			// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
			break
		}
		hasUpper = hasUpper || ('A' <= c && c <= 'Z')
		// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
	}

	if isASCII { // optimize for ASCII-only byte slices.
		if !hasUpper {
			//gobra:rewrite 809fce13cf126b5d13fbdc83dce3ac240bff2bc5872ee55fc30a55d6ed66ec8d
			//gobra:cont 			return append( /* @ perm(R40), @ */ []byte(""), s...)
			//gobra:end-old-code 809fce13cf126b5d13fbdc83dce3ac240bff2bc5872ee55fc30a55d6ed66ec8d
			// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
			res = append( /* @ perm(R40), @ */ []byte(""), s...)
			// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
			return res
			//gobra:endrewrite 809fce13cf126b5d13fbdc83dce3ac240bff2bc5872ee55fc30a55d6ed66ec8d
		}
		b := make([]byte, len(s))
		// @ invariant acc(sl.Bytes(s, 0, len(s)), R40)
		// @ invariant forall j int :: {&b[j]} 0 <= j && j < len(b) ==> acc(&b[j], 1)
		// @ invariant InRangeInc(i, 0, len(s))
		// @ decreases len(s) - i
		for i := 0; i < len(s); i++ {
			// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
			c := s[i]
			if 'A' <= c && c <= 'Z' {
				c += 'a' - 'A'
			}
			b[i] = c
			// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
		}
		return b
	}
	return Map(unicode.ToLower, s)
}

// ToTitle treats s as UTF-8-encoded bytes and returns a copy with all the Unicode letters mapped to their title case.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ decreases
func ToTitle(s []byte) []byte { return Map(unicode.ToTitle, s) }

// ToUpperSpecial treats s as UTF-8-encoded bytes and returns a copy with all the Unicode letters mapped to their
// upper case, giving priority to the special casing rules.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ decreases
func ToUpperSpecial(c unicode.SpecialCase, s []byte) []byte {
	return Map(c.ToUpper, s)
}

// ToLowerSpecial treats s as UTF-8-encoded bytes and returns a copy with all the Unicode letters mapped to their
// lower case, giving priority to the special casing rules.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ decreases
func ToLowerSpecial(c unicode.SpecialCase, s []byte) []byte {
	return Map(c.ToLower, s)
}

// ToTitleSpecial treats s as UTF-8-encoded bytes and returns a copy with all the Unicode letters mapped to their
// title case, giving priority to the special casing rules.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ decreases
func ToTitleSpecial(c unicode.SpecialCase, s []byte) []byte {
	return Map(c.ToTitle, s)
}

// ToValidUTF8 treats s as UTF-8-encoded bytes and returns a copy with each run of bytes
// representing invalid UTF-8 replaced with the bytes in replacement, which may be empty.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
// @ preserves acc(sl.Bytes(replacement, 0, len(replacement)), R40)
//
// @ decreases
func ToValidUTF8(s, replacement []byte) []byte {
	b := make([]byte, 0, len(s)+len(replacement))
	invalid := false // previous byte was from an invalid UTF-8 sequence
	// @ fold sl.Bytes(b, 0, len(b))
	// @ invariant acc(sl.Bytes(s, 0, len(s)), R40)
	// @ invariant acc(sl.Bytes(replacement, 0, len(replacement)), R40)
	// @ invariant sl.Bytes(b, 0, len(b))
	// @ invariant i >= 0
	// @ decreases len(s) - i
	for i := 0; i < len(s); {
		// @ unfold sl.Bytes(b, 0, len(b))
		// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
		c := s[i]
		if c < utf8.RuneSelf {
			i++
			invalid = false
			b = append( /* @ R50, @ */ b, c)
			// @ fold sl.Bytes(b, 0, len(b))
			// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
			continue
		}
		// @ assert forall j int :: {&s[i:][j]} 0 <= j && j < len(s[i:]) ==> &s[i:][j] == &s[j+i]
		// @ fold acc(sl.Bytes(s[i:], 0, len(s[i:])), R40)
		_, wid := utf8.DecodeRune(s[i:])
		// @ unfold acc(sl.Bytes(s[i:], 0, len(s[i:])), R40)
		if wid == 1 {
			i++
			if !invalid {
				invalid = true
				// @ unfold acc(sl.Bytes(replacement, 0, len(replacement)), R40)
				b = append( /* @ R50, @ */ b, replacement...)
				// @ fold acc(sl.Bytes(replacement, 0, len(replacement)), R40)
			}
			// @ fold sl.Bytes(b, 0, len(b))
			// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
			continue
		}
		invalid = false
		b = append( /* @ R50, @ */ b, s[i:i+wid]...)
		i += wid
		// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
		// @ fold sl.Bytes(b, 0, len(b))
	}
	return b
}

// isSeparator reports whether the rune could mark a word boundary.
// TODO: update when package unicode captures more of the properties.
//
// @ decreases
func isSeparator(r rune) bool {
	// ASCII alphanumerics and underscore are not separators
	if r <= 0x7F {
		switch {
		case '0' <= r && r <= '9':
			return false
		case 'a' <= r && r <= 'z':
			return false
		case 'A' <= r && r <= 'Z':
			return false
		case r == '_':
			return false
		}
		return true
	}
	// Letters and digits are not separators
	if unicode.IsLetter(r) || unicode.IsDigit(r) {
		return false
	}
	// Otherwise, all we can do for now is treat spaces as separators.
	return unicode.IsSpace(r)
}

// Title treats s as UTF-8-encoded bytes and returns a copy with all Unicode letters that begin
// words mapped to their title case.
//
// Deprecated: The rule Title uses for word boundaries does not handle Unicode
// punctuation properly. Use golang.org/x/text/cases instead.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ decreases
func Title(s []byte) []byte {
	// Use a closure here to remember state.
	// Hackish but effective. Depends on Map scanning in order and calling
	// the closure once per rune.
	//gobra:rewrite 57cdbb2883069d87da174cc47c5314dc472c379e28b6cc0810de5833e53cdea9
	//gobra:cont 	prev := ' '
	//gobra:end-old-code 57cdbb2883069d87da174cc47c5314dc472c379e28b6cc0810de5833e53cdea9
	prev /* @ @ @ */ := rune(' ')
	//gobra:endrewrite 57cdbb2883069d87da174cc47c5314dc472c379e28b6cc0810de5833e53cdea9
	return Map(
		// @ requires acc(&prev)
		//
		// @ decreases
		func(r rune) rune {
			if isSeparator(prev) {
				prev = r
				return unicode.ToTitle(r)
			}
			prev = r
			return r
		},
		s)
}

// TrimLeftFunc treats s as UTF-8-encoded bytes and returns a subslice of s by slicing off
// all leading UTF-8-encoded code points c that satisfy f(c).
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ ensures (len(res) == 0) == (idx == -1)
//
// @ ensures res != nil ==> (0 <= idx && idx < len(s))
//
// @ ensures res != nil ==> (forall j int :: {&s[idx:][j]} 0 <= j && j < len(s[idx:]) ==> &s[idx:][j] == &res[j])
//
// @ decreases
func TrimLeftFunc(s []byte, f func(r rune) bool) (res []byte /*@, ghost idx int @*/) {
	i := indexFunc(s, f, false)
	if i == -1 {
		return nil // @ , -1
	}
	return s[i:] // @ , i
}

// TrimRightFunc returns a subslice of s by slicing off all trailing
// UTF-8-encoded code points c that satisfy f(c).
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ ensures 0 <= idx && idx <= len(s)
//
// @ ensures forall j int :: {&s[:idx][j]} 0 <= j && j < len(s[:idx]) ==> &s[:idx][j] == &res[j]
//
// @ decreases
func TrimRightFunc(s []byte, f func(r rune) bool) (res []byte /*@ , ghost idx int @*/) {
	i := lastIndexFunc(s, f, false)
	// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
	if i >= 0 && s[i] >= utf8.RuneSelf {
		// @ assert forall j int :: {&s[i:][j]} 0 <= j && j < len(s[i:]) ==> &s[i:][j] == &s[j+i]
		// @ fold acc(sl.Bytes(s[i:], 0, len(s[i:])), R40)
		_, wid := utf8.DecodeRune(s[i:])
		// @ unfold acc(sl.Bytes(s[i:], 0, len(s[i:])), R40)
		i += wid
	} else {
		i++
	}
	// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
	return s[0:i] // @ , i
}

// TrimFunc returns a subslice of s by slicing off all leading and trailing
// UTF-8-encoded code points c that satisfy f(c).
// @ trusted
// @ decreases
func TrimFunc(s []byte, f func(r rune) bool) []byte {
	return TrimRightFunc(TrimLeftFunc(s, f), f)
}

// TrimPrefix returns s without the provided leading prefix string.
// If s doesn't start with prefix, s is returned unchanged.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ preserves acc(sl.Bytes(prefix, 0, len(prefix)), R40)
//
// @ decreases
func TrimPrefix(s, prefix []byte) []byte {
	if HasPrefix(s, prefix) {
		return s[len(prefix):]
	}
	return s
}

// TrimSuffix returns s without the provided trailing suffix string.
// If s doesn't end with suffix, s is returned unchanged.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ preserves acc(sl.Bytes(suffix, 0, len(suffix)), R40)
//
// @ decreases
func TrimSuffix(s, suffix []byte) []byte {
	if HasSuffix(s, suffix) {
		return s[:len(s)-len(suffix)]
	}
	return s
}

// IndexFunc interprets s as a sequence of UTF-8-encoded code points.
// It returns the byte index in s of the first Unicode
// code point satisfying f(c), or -1 if none do.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ decreases
func IndexFunc(s []byte, f func(r rune) bool) int {
	return indexFunc(s, f, true)
}

// LastIndexFunc interprets s as a sequence of UTF-8-encoded code points.
// It returns the byte index in s of the last Unicode
// code point satisfying f(c), or -1 if none do.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ decreases
func LastIndexFunc(s []byte, f func(r rune) bool) int {
	return lastIndexFunc(s, f, true)
}

// indexFunc is the same as IndexFunc except that if
// truth==false, the sense of the predicate function is
// inverted.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ ensures res == -1 || (0 <= res && res < len(s))
//
// @ decreases
//
// @ trusted
func indexFunc(s []byte, f func(r rune) bool, truth bool) (res int) {
	start := 0
	for start < len(s) {
		wid := 1
		r := rune(s[start])
		if r >= utf8.RuneSelf {
			r, wid = utf8.DecodeRune(s[start:])
		}
		if f(r) == truth {
			return start
		}
		start += wid
	}
	return -1
}

// lastIndexFunc is the same as LastIndexFunc except that if
// truth==false, the sense of the predicate function is
// inverted.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ ensures -1 <= res && res < len(s)
//
// @ decreases
//
// @ trusted
func lastIndexFunc(s []byte, f func(r rune) bool, truth bool) (res int) {
	for i := len(s); i > 0; {
		r, size := rune(s[i-1]), 1
		if r >= utf8.RuneSelf {
			r, size = utf8.DecodeLastRune(s[0:i])
		}
		i -= size
		if f(r) == truth {
			return i
		}
	}
	return -1
}

// asciiSet is a 32-byte value, where each bit represents the presence of a
// given ASCII character in the set. The 128-bits of the lower 16 bytes,
// starting with the least-significant bit of the lowest word to the
// most-significant bit of the highest word, map to the full range of all
// 128 ASCII characters. The 128-bits of the upper 16 bytes will be zeroed,
// ensuring that any non-ASCII character will be reported as not in the set.
// This allocates a total of 32 bytes even though the upper half
// is unused to avoid bounds checks in asciiSet.contains.
type asciiSet [8]uint32

// makeASCIISet creates a set of ASCII characters and reports whether all
// characters in chars are ASCII.
//
// @ trusted
//
//gobra:rewrite 976a483f32dd9f1734093b6a51f1c1e7cd6c20c3d1b7e2707ce1d6b6d3ccf908
//gobra:cont func makeASCIISet(chars string) (as asciiSet, ok bool) {
//gobra:cont 	for i := 0; i < len(chars); i++ {
//gobra:cont 		c := chars[i]
//gobra:cont 		if c >= utf8.RuneSelf {
//gobra:cont 			return as, false
//gobra:cont 		}
//gobra:cont 		as[c/32] |= 1 << (c % 32)
//gobra:cont 	}
//gobra:cont 	return as, true
//gobra:cont }
//gobra:end-old-code 976a483f32dd9f1734093b6a51f1c1e7cd6c20c3d1b7e2707ce1d6b6d3ccf908
func makeASCIISet(chars string) (asc asciiSet, ok bool) {
	for i := 0; i < len(chars); i++ {
		c := chars[i]
		if c >= utf8.RuneSelf {
			return asc, false
		}
		asc[c/32] |= 1 << (c % 32)
	}
	return asc, true
}

//gobra:endrewrite 976a483f32dd9f1734093b6a51f1c1e7cd6c20c3d1b7e2707ce1d6b6d3ccf908

// contains reports whether c is inside the set.
//
// @ trusted
// @ decreases
//
//gobra:rewrite 0f0ebbd7ca470d581fd1af46ca0cfe9b2ac2c405c24300860944b852a7de1dc5
//gobra:cont func (as *asciiSet) contains(c byte) bool {
//gobra:cont 	return (as[c/32] & (1 << (c % 32))) != 0
//gobra:cont }
//gobra:end-old-code 0f0ebbd7ca470d581fd1af46ca0cfe9b2ac2c405c24300860944b852a7de1dc5
func (asc *asciiSet) contains(c byte) bool {
	return (asc[c/32] & (1 << (c % 32))) != 0
}

//gobra:endrewrite 0f0ebbd7ca470d581fd1af46ca0cfe9b2ac2c405c24300860944b852a7de1dc5

// containsRune is a simplified version of strings.ContainsRune
// to avoid importing the strings package.
// We avoid bytes.ContainsRune to avoid allocating a temporary copy of s.
// @ trusted
// @ decreases
func containsRune(s string, r rune) bool {
	for _, c := range s {
		if c == r {
			return true
		}
	}
	return false
}

// Trim returns a subslice of s by slicing off all leading and
// trailing UTF-8-encoded code points contained in cutset.
// @ trusted
func Trim(s []byte, cutset string) []byte {
	if len(s) == 0 {
		// This is what we've historically done.
		return nil
	}
	if cutset == "" {
		return s
	}
	if len(cutset) == 1 && cutset[0] < utf8.RuneSelf {
		return trimLeftByte(trimRightByte(s, cutset[0]), cutset[0])
	}
	//gobra:rewrite 329e1a6db3db57138d21cb1ecb7578a2c511353b2a38ea13e4d95797885d2652
	//gobra:cont 	if as, ok := makeASCIISet(cutset); ok {
	//gobra:cont 		return trimLeftASCII(trimRightASCII(s, &as), &as)
	//gobra:end-old-code 329e1a6db3db57138d21cb1ecb7578a2c511353b2a38ea13e4d95797885d2652
	if asc, ok := makeASCIISet(cutset); ok {
		return trimLeftASCII(trimRightASCII(s, &asc), &asc)
		//gobra:endrewrite 329e1a6db3db57138d21cb1ecb7578a2c511353b2a38ea13e4d95797885d2652
	}
	return trimLeftUnicode(trimRightUnicode(s, cutset), cutset)
}

// TrimLeft returns a subslice of s by slicing off all leading
// UTF-8-encoded code points contained in cutset.
// @ trusted
func TrimLeft(s []byte, cutset string) []byte {
	if len(s) == 0 {
		// This is what we've historically done.
		return nil
	}
	if cutset == "" {
		return s
	}
	if len(cutset) == 1 && cutset[0] < utf8.RuneSelf {
		return trimLeftByte(s, cutset[0])
	}
	//gobra:rewrite 02e8fa567eed1a77793874c0a530f453e89ef951a7e1262e8af97f1d29b0e426
	//gobra:cont 	if as, ok := makeASCIISet(cutset); ok {
	//gobra:cont 		return trimLeftASCII(s, &as)
	//gobra:end-old-code 02e8fa567eed1a77793874c0a530f453e89ef951a7e1262e8af97f1d29b0e426
	if asc, ok := makeASCIISet(cutset); ok {
		return trimLeftASCII(s, &asc)
		//gobra:endrewrite 02e8fa567eed1a77793874c0a530f453e89ef951a7e1262e8af97f1d29b0e426
	}
	return trimLeftUnicode(s, cutset)
}

// @ preserves forall i int :: {&s[i]} 0 <= i && i < len(s) ==> acc(&s[i], _)
func trimLeftByte(s []byte, c byte) []byte {
	// @ invariant forall i int :: {&s[i]} 0 <= i && i < len(s) ==> acc(&s[i], _)
	for len(s) > 0 && s[0] == c {
		// @ assert forall i int :: {&s[1:][i]} 0 <= i && i < len(s[1:]) ==> &s[1:][i] == &s[i+1]
		s = s[1:]
	}
	if len(s) == 0 {
		// This is what we've historically done.
		return nil
	}
	return s
}

// @ preserves forall i int :: {&s[i]} 0 <= i && i < len(s) ==> acc(&s[i], _)
//
// @ preserves acc(asc, _)
//
// @ decreases
//
//gobra:rewrite 0387089c2272afa3e2a8a1a4875bb9c5c94815f4578982adbe8355e0dc4bb562
//gobra:cont func trimLeftASCII(s []byte, as *asciiSet) []byte {
//gobra:cont 	for len(s) > 0 {
//gobra:cont 		if !as.contains(s[0]) {
//gobra:end-old-code 0387089c2272afa3e2a8a1a4875bb9c5c94815f4578982adbe8355e0dc4bb562
func trimLeftASCII(s []byte, asc *asciiSet) []byte {
	// @ invariant forall i int :: {&s[i]} 0 <= i && i < len(s) ==> acc(&s[i], _)
	// @ invariant acc(asc, _)
	// @ decreases len(s)
	for len(s) > 0 {
		if !asc.contains(s[0]) {
			//gobra:endrewrite 0387089c2272afa3e2a8a1a4875bb9c5c94815f4578982adbe8355e0dc4bb562
			break
		}
		// @ assert forall i int :: {&s[1:][i]} 0 <= i && i < len(s[1:]) ==> &s[1:][i] == &s[i+1]
		s = s[1:]
	}
	if len(s) == 0 {
		// This is what we've historically done.
		return nil
	}
	return s
}

// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ decreases
func trimLeftUnicode(s []byte, cutset string) []byte {
	// @ ghost olds := s
	// @ ghost idx := 0
	// @ invariant 0 <= idx && idx <= len(olds)
	// @ invariant olds[idx:] === s
	// @ invariant acc(sl.Bytes(olds, 0, len(olds)), R40)
	// @ decreases len(s)
	for len(s) > 0 {
		// @ unfold acc(sl.Bytes(olds, 0, len(olds)), R40)
		// @ assert forall j int :: {&olds[idx:][j]} 0 <= j && j < len(olds[idx:]) ==> &olds[idx:][j] == &olds[j+idx]
		r, n := rune(s[0]), 1
		if r >= utf8.RuneSelf {
			// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
			r, n = utf8.DecodeRune(s)
			// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
		}
		if !containsRune(cutset, r) {
			// @ fold acc(sl.Bytes(olds, 0, len(olds)), R40)
			break
		}
		s = s[n:]
		// @ idx += n
		// @ fold acc(sl.Bytes(olds, 0, len(olds)), R40)
	}
	if len(s) == 0 {
		// This is what we've historically done.
		return nil
	}
	return s
}

// TrimRight returns a subslice of s by slicing off all trailing
// UTF-8-encoded code points that are contained in cutset.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ trusted
func TrimRight(s []byte, cutset string) []byte {
	if len(s) == 0 || cutset == "" {
		return s
	}
	if len(cutset) == 1 && cutset[0] < utf8.RuneSelf {
		return trimRightByte(s, cutset[0])
	}
	//gobra:rewrite 6b32179dcd0024634836ba05365a9b23b3c72a83392c21e0d427fcbef33f3335
	//gobra:cont 	if as, ok := makeASCIISet(cutset); ok {
	//gobra:cont 		return trimRightASCII(s, &as)
	//gobra:end-old-code 6b32179dcd0024634836ba05365a9b23b3c72a83392c21e0d427fcbef33f3335
	if asc, ok := makeASCIISet(cutset); ok {
		return trimRightASCII(s, &asc)
		//gobra:endrewrite 6b32179dcd0024634836ba05365a9b23b3c72a83392c21e0d427fcbef33f3335
	}
	return trimRightUnicode(s, cutset)
}

// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ decreases
func trimRightByte(s []byte, c byte) []byte {
	//gobra:rewrite 31b9f02d21540a41351d8bce67a9db8399d8c59e6312bcf5ebe870692897747f
	//gobra:cont 	for len(s) > 0 && s[len(s)-1] == c {
	//gobra:cont 		s = s[:len(s)-1]
	//gobra:cont 	}
	//gobra:end-old-code 31b9f02d21540a41351d8bce67a9db8399d8c59e6312bcf5ebe870692897747f
	// @ ghost olds := s
	// @ ghost idx := len(s)
	// @ invariant 0 <= idx && idx <= len(olds)
	// @ invariant olds[:idx] === s
	// @ invariant acc(sl.Bytes(olds, 0, len(olds)), R40)
	// @ decreases len(s)
	for len(s) > 0 && /* @ unfolding acc(sl.Bytes(olds, 0, len(olds)), R40) in @ */ s[len(s)-1] == c {
		// @ unfold acc(sl.Bytes(olds, 0, len(olds)), R40)
		// @ idx = len(s)-1
		s = s[:len(s)-1]
		// @ fold acc(sl.Bytes(olds, 0, len(olds)), R40)
	}
	//gobra:endrewrite 31b9f02d21540a41351d8bce67a9db8399d8c59e6312bcf5ebe870692897747f
	return s
}

// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ preserves acc(asc, R40)
//
// @ decreases
//
//gobra:rewrite 8c5e716b23a66f72365a9505e211ec2676a538b1b7f603a6a87fa45a9448fab6
//gobra:cont func trimRightASCII(s []byte, as *asciiSet) []byte {
//gobra:cont 	for len(s) > 0 {
//gobra:cont 		if !as.contains(s[len(s)-1]) {
//gobra:end-old-code 8c5e716b23a66f72365a9505e211ec2676a538b1b7f603a6a87fa45a9448fab6
func trimRightASCII(s []byte, asc *asciiSet) []byte {
	// @ ghost olds := s
	// @ ghost idx := len(s)
	// @ invariant 0 <= idx && idx <= len(olds)
	// @ invariant olds[:idx] === s
	// @ invariant acc(sl.Bytes(olds, 0, len(olds)), R40)
	// @ invariant acc(asc, R40)
	// @ decreases len(s)
	for len(s) > 0 {
		// @ unfold acc(sl.Bytes(olds, 0, len(olds)), R40)
		if !asc.contains(s[len(s)-1]) {
			// @ fold acc(sl.Bytes(olds, 0, len(olds)), R40)
			//gobra:endrewrite 8c5e716b23a66f72365a9505e211ec2676a538b1b7f603a6a87fa45a9448fab6
			break
		}
		// @ idx = len(s)-1
		s = s[:len(s)-1]
		// @ fold acc(sl.Bytes(olds, 0, len(olds)), R40)
	}
	return s
}

// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ decreases
func trimRightUnicode(s []byte, cutset string) []byte {
	// @ ghost olds := s
	// @ ghost idx := len(s)
	// @ invariant 0 <= idx && idx <= len(olds)
	// @ invariant olds[:idx] === s
	// @ invariant acc(sl.Bytes(olds, 0, len(olds)), R40)
	// @ decreases len(s)
	for len(s) > 0 {
		// @ unfold acc(sl.Bytes(olds, 0, len(olds)), R40)
		r, n := rune(s[len(s)-1]), 1
		if r >= utf8.RuneSelf {
			r, n = utf8.DecodeLastRune(s)
		}
		if !containsRune(cutset, r) {
			// @ fold acc(sl.Bytes(olds, 0, len(olds)), R40)
			break
		}
		// @ idx = len(s)-n
		s = s[:len(s)-n]
		// @ fold acc(sl.Bytes(olds, 0, len(olds)), R40)
	}
	return s
}

// TrimSpace returns a subslice of s by slicing off all leading and
// trailing white space, as defined by Unicode.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ decreases
func TrimSpace(s []byte) (res []byte) {
	// Fast path for ASCII: look for the first ASCII non-space byte
	start := 0
	// @ invariant acc(sl.Bytes(s, 0, len(s)), R40)
	// @ invariant 0 <= start && start <= len(s)
	// @ decreases len(s) - start
	for ; start < len(s); start++ {
		// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
		c := s[start]
		if c >= utf8.RuneSelf {
			// If we run into a non-ASCII byte, fall back to the
			// slower unicode-aware method on the remaining bytes
			//gobra:rewrite b208b2fc84fdec6980efcf6edd6d2e889e1c30b2f474d6c0f45409e7fcac7947
			//gobra:cont 			return TrimFunc(s[start:], unicode.IsSpace)
			//gobra:end-old-code b208b2fc84fdec6980efcf6edd6d2e889e1c30b2f474d6c0f45409e7fcac7947
			// @ assert forall i int :: {&s[start:][i]} 0 <= i && i < len(s[start:]) ==> &s[start:][i] == &s[i+start]
			// @ fold acc(sl.Bytes(s[start:], 0, len(s[start:])), R40)
			res = TrimFunc(s[start:], unicode.IsSpace)
			// @ unfold acc(sl.Bytes(s[start:], 0, len(s[start:])), R40)
			// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
			return res
			//gobra:endrewrite b208b2fc84fdec6980efcf6edd6d2e889e1c30b2f474d6c0f45409e7fcac7947
		}
		// @ b.ByteValue(c)
		if asciiSpace[c] == 0 {
			// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
			break
		}
		// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
	}

	// Now look for the first ASCII non-space byte from the end
	stop := len(s)
	// @ oldStart := start
	// @ invariant acc(sl.Bytes(s, 0, len(s)), R40)
	// @ invariant 0 <= start && start <= len(s)
	// @ invariant old(start) == start
	// @ invariant start == oldStart
	// @ invariant stop <= len(s)
	// @ invariant start <= stop
	// @ decreases stop - start
	for ; stop > start; stop-- {
		// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
		c := s[stop-1]
		// @ b.ByteValue(c)
		if c >= utf8.RuneSelf {
			// @ assert forall i int :: {&s[start:stop][i]} 0 <= i && i < len(s[start:stop]) ==> &s[start:stop][i] == &s[i+start]
			//gobra:rewrite a3f298cff5d32351f7602fe0f87e35604223b1ccb74508953fa6c004bb35b87a
			//gobra:cont 			return TrimFunc(s[start:stop], unicode.IsSpace)
			//gobra:end-old-code a3f298cff5d32351f7602fe0f87e35604223b1ccb74508953fa6c004bb35b87a
			// @ fold acc(sl.Bytes(s[start:stop], 0, len(s[start:stop])), R40)
			res = TrimFunc(s[start:stop], unicode.IsSpace)
			// @ unfold acc(sl.Bytes(s[start:stop], 0, len(s[start:stop])), R40)
			// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
			return res
			//gobra:endrewrite a3f298cff5d32351f7602fe0f87e35604223b1ccb74508953fa6c004bb35b87a
		}
		// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
		if asciiSpace[c] == 0 {
			break
		}
	}

	// At this point s[start:stop] starts and ends with an ASCII
	// non-space bytes, so we're done. Non-ASCII cases have already
	// been handled above.
	if start == stop {
		// Special case to preserve previous TrimLeftFunc behavior,
		// returning nil instead of empty slice if all spaces.
		return nil
	}
	return s[start:stop]
}

// Runes interprets s as a sequence of UTF-8-encoded code points.
// It returns a slice of runes (Unicode code points) equivalent to s.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ ensures rsl.Runes(res, 0, len(res))
//
// @ ensures rsl.ViewRunes(res) == utf8.Codepoints(s)
//
// @ decreases
func Runes(s []byte) (res []rune) {
	//gobra:rewrite 5aab27295fdb5ccf8c220250bc5b75224bfd961a47a286501fad584575d50cda
	//gobra:cont 	t := make([]rune, utf8.RuneCount(s))
	//gobra:end-old-code 5aab27295fdb5ccf8c220250bc5b75224bfd961a47a286501fad584575d50cda
	tLength /* @, indices @*/ := utf8.RuneCount(s)
	t := make([]rune, tLength)
	//gobra:endrewrite 5aab27295fdb5ccf8c220250bc5b75224bfd961a47a286501fad584575d50cda
	i := 0

	// @ ghost olds := s
	// @ ghost idx := 0
	// @ ghost codepoints := utf8.Codepoints(s)
	// @ fold rsl.Runes(t, 0, len(t))
	// @ invariant i <= idx
	// @ invariant 0 <= idx && idx <= len(olds)
	// @ invariant acc(sl.Bytes(olds, 0, len(olds)), R40)
	// @ invariant olds[idx:] === s
	// @ invariant rsl.Runes(t, 0, len(t))
	// @ invariant utf8.Codepoints(s) == codepoints[i:]
	// @ invariant 0 <= i && i <= len(t)
	// @ invariant i == len(t) - len(utf8.Codepoints(s))
	// @ invariant len(s) > 0 ==> i < len(t)
	// @ invariant rsl.ViewRunes(t)[:i] == codepoints[:i]
	// @ decreases len(s)
	for len(s) > 0 {
		// @ unfold rsl.Runes(t, 0, len(t))
		// @ unfold acc(sl.Bytes(olds, 0, len(olds)), R40)
		// @ assert forall j int :: {&olds[idx:][j]} 0 <= j && j < len(olds[idx:]) ==> &olds[idx:][j] == &olds[j+idx]
		// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
		r, l := utf8.DecodeRune(s)
		// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
		t[i] = r
		i++
		s = s[l:]
		// @ idx += l
		// @ fold acc(sl.Bytes(olds, 0, len(olds)), R40)
		// @ fold rsl.Runes(t, 0, len(t))
	}
	return t
}

// Replace returns a copy of the slice s with the first n
// non-overlapping instances of old replaced by new.
// If old is empty, it matches at the beginning of the slice
// and after each UTF-8 sequence, yielding up to k+1 replacements
// for a k-rune slice.
// If n < 0, there is no limit on the number of replacements.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ preserves acc(sl.Bytes(oldval, 0, len(oldval)), R40)
//
// @ preserves acc(sl.Bytes(newval, 0, len(newval)), R40)
//
// @ decreases
//
// @ trusted
//
//gobra:rewrite 97d56fc6453211521dade272298f0508c52e5884a5900aa9e86582e4e7cfd59f
//gobra:cont func Replace(s, old, new []byte, n int) []byte {
//gobra:end-old-code 97d56fc6453211521dade272298f0508c52e5884a5900aa9e86582e4e7cfd59f
func Replace(s, oldval, newval []byte, n int) (res []byte) {
	//gobra:endrewrite 97d56fc6453211521dade272298f0508c52e5884a5900aa9e86582e4e7cfd59f
	m := 0
	if n != 0 {
		// Compute number of replacements.
		//gobra:rewrite d201f42888b2fb247d6f7dd72386a7cdc829fb1878e152fdf84508118901575d
		//gobra:cont 		m = Count(s, old)
		//gobra:end-old-code d201f42888b2fb247d6f7dd72386a7cdc829fb1878e152fdf84508118901575d
		m /* @, _ @ */ = Count(s, oldval)
		//gobra:endrewrite d201f42888b2fb247d6f7dd72386a7cdc829fb1878e152fdf84508118901575d
	}
	if m == 0 {
		// Just return a copy.
		//gobra:rewrite 918b6bf86b6e1ca9ad4e6d479eb9d5e43e5144ca22bdd91d826ce77fb1a17594
		//gobra:cont 		return append( /* @ R40,  @ */ []byte(nil), s...)
		//gobra:end-old-code 918b6bf86b6e1ca9ad4e6d479eb9d5e43e5144ca22bdd91d826ce77fb1a17594

		// @ unfold acc(sl.Bytes(s, 0, len(s)), R40)
		res = append( /* @ R40, @ */ []byte(nil), s...)
		// @ fold acc(sl.Bytes(s, 0, len(s)), R40)
		return res
		//gobra:endrewrite 918b6bf86b6e1ca9ad4e6d479eb9d5e43e5144ca22bdd91d826ce77fb1a17594
	}
	if n < 0 || m < n {
		n = m
	}

	// Apply replacements to buffer.
	//gobra:rewrite c787ef8de608ddf205718721d556dee5a732bac8dce3fa92ce9f2266fe7bc2a1
	//gobra:cont 	t := make([]byte, len(s)+n*(len(new)-len(old)))
	//gobra:end-old-code c787ef8de608ddf205718721d556dee5a732bac8dce3fa92ce9f2266fe7bc2a1
	t := make([]byte, len(s)+n*(len(newval)-len(oldval)))
	//gobra:endrewrite c787ef8de608ddf205718721d556dee5a732bac8dce3fa92ce9f2266fe7bc2a1
	w := 0
	start := 0
	for i := 0; i < n; i++ {
		j := start
		//gobra:rewrite 945fbe50b78d9a29bb15d5eaedeaf126427abf5df5d10795b8c3eae67c53cab9
		//gobra:cont 		if len(old) == 0 {
		//gobra:end-old-code 945fbe50b78d9a29bb15d5eaedeaf126427abf5df5d10795b8c3eae67c53cab9
		if len(oldval) == 0 {
			//gobra:endrewrite 945fbe50b78d9a29bb15d5eaedeaf126427abf5df5d10795b8c3eae67c53cab9
			if i > 0 {
				_, wid := utf8.DecodeRune(s[start:])
				j += wid
			}
		} else {
			//gobra:rewrite c485492729f4eaac8633c92b5d0f51e439032888b93389e82c6b2202e864ca4b
			//gobra:cont 			j += Index(s[start:], old)
			//gobra:end-old-code c485492729f4eaac8633c92b5d0f51e439032888b93389e82c6b2202e864ca4b
			j += Index(s[start:], oldval)
			//gobra:endrewrite c485492729f4eaac8633c92b5d0f51e439032888b93389e82c6b2202e864ca4b
		}
		w += copy(t[w:], s[start:j] /* @, R40 @ */)
		//gobra:rewrite 192a485aaa164f7b2c5f7c7f1833b5d50b78f226160b2cac46692dc4a7bedb30
		//gobra:cont 		w += copy(t[w:], new)
		//gobra:cont 		start = j + len(old)
		//gobra:end-old-code 192a485aaa164f7b2c5f7c7f1833b5d50b78f226160b2cac46692dc4a7bedb30
		w += copy(t[w:], newval /* @, R40 @ */)
		start = j + len(oldval)
		//gobra:endrewrite 192a485aaa164f7b2c5f7c7f1833b5d50b78f226160b2cac46692dc4a7bedb30
	}
	w += copy(t[w:], s[start:] /* @, R40 @ */)
	return t[0:w]
}

// ReplaceAll returns a copy of the slice s with all
// non-overlapping instances of old replaced by new.
// If old is empty, it matches at the beginning of the slice
// and after each UTF-8 sequence, yielding up to k+1 replacements
// for a k-rune slice.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ preserves acc(sl.Bytes(oldval, 0, len(oldval)), R40)
//
// @ preserves acc(sl.Bytes(newval, 0, len(newval)), R40)
//
// @ decreases
//
//gobra:rewrite 97c2ede7687475e639eb6cf004d3abccbd534c90686609842d241e0faf3710c5
//gobra:cont func ReplaceAll(s, old, new []byte) []byte {
//gobra:cont 	return Replace(s, old, new, -1)
//gobra:cont }
//gobra:end-old-code 97c2ede7687475e639eb6cf004d3abccbd534c90686609842d241e0faf3710c5
func ReplaceAll(s, oldval, newval []byte) []byte {
	return Replace(s, oldval, newval, -1)
}

// EqualFold reports whether s and t, interpreted as UTF-8 strings,
// are equal under simple Unicode case-folding, which is a more general
// form of case-insensitivity.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ preserves acc(sl.Bytes(t, 0, len(t)), R40)
//
// @ // we cannot yet verify the body of this function, since it contains `goto`: see gobra issue #783
func EqualFold(s, t []byte) bool /* {
	// ASCII fast path
	i := 0
	for ; i < len(s) && i < len(t); i++ {
		sr := s[i]
		tr := t[i]
		if sr|tr >= utf8.RuneSelf {
			goto hasUnicode
		}

		// Easy case.
		if tr == sr {
			continue
		}

		// Make sr < tr to simplify what follows.
		if tr < sr {
			tr, sr = sr, tr
		}
		// ASCII only, sr/tr must be upper/lower case
		if 'A' <= sr && sr <= 'Z' && tr == sr+'a'-'A' {
			continue
		}
		return false
	}
	// Check if we've exhausted both strings.
	return len(s) == len(t)

hasUnicode:
	s = s[i:]
	t = t[i:]
	for len(s) != 0 && len(t) != 0 {
		// Extract first rune from each.
		var sr, tr rune
		if s[0] < utf8.RuneSelf {
			sr, s = rune(s[0]), s[1:]
		} else {
			r, size := utf8.DecodeRune(s)
			sr, s = r, s[size:]
		}
		if t[0] < utf8.RuneSelf {
			tr, t = rune(t[0]), t[1:]
		} else {
			r, size := utf8.DecodeRune(t)
			tr, t = r, t[size:]
		}

		// If they match, keep going; if not, return false.

		// Easy case.
		if tr == sr {
			continue
		}

		// Make sr < tr to simplify what follows.
		if tr < sr {
			tr, sr = sr, tr
		}
		// Fast check for ASCII.
		if tr < utf8.RuneSelf {
			// ASCII only, sr/tr must be upper/lower case
			if 'A' <= sr && sr <= 'Z' && tr == sr+'a'-'A' {
				continue
			}
			return false
		}

		// General case. SimpleFold(x) returns the next equivalent rune > x
		// or wraps around to smaller values.
		r := unicode.SimpleFold(sr)
		for r != sr && r < tr {
			r = unicode.SimpleFold(r)
		}
		if r == tr {
			continue
		}
		return false
	}

	// One string is empty. Are both?
	return len(s) == len(t)
} */

// Index returns the index of the first instance of sep in s, or -1 if sep is not present in s.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ preserves acc(sl.Bytes(sep, 0, len(sep)), R40)
//
// @ ensures res == -1 || (0 <= res && res + len(sep) <= len(s))
//
// @ ensures res != -1 ==> forall i int :: {&s[res:res+len(sep)][i]}{&s[i+res]} 0 <= i && i < len(s[res:res+len(sep)]) ==> &s[res:res+len(sep)][i] == &s[i+res]
//
// @ ensures res != -1 ==> View(s)[res:res+len(sep)] == View(sep)
//
// # this property is not verified (yet)
// @ ensures res != -1 ==> forall i int :: {View(s)[i:i+len(sep)]} 0 <= i && i < res ==> View(s)[i:i+len(sep)] != View(sep)
//
// @ ensures res == -1 ==> forall i int :: {View(s)[i:i+len(sep)]} 0 <= i && i + len(sep) <= len(s) ==> View(s)[i:i+len(sep)] != View(sep)
//
// @ decreases
func Index(s, sep []byte) (res int) {
	n := len(sep)
	switch {
	case n == 0:
		return 0
	case n == 1:
		//gobra:rewrite e4ce06c882699aa24a46ac5f5ed3a2d1331f7d8c7b2a871c9ffe07721bfb9039
		//gobra:cont 		return IndexByte(s,
		//gobra:cont 			/* @ unfolding acc(sl.Bytes(sep, 0, len(sep)), R40) in @ */ sep[0])
		//gobra:end-old-code e4ce06c882699aa24a46ac5f5ed3a2d1331f7d8c7b2a871c9ffe07721bfb9039
		res = IndexByte(s,
			/* @ unfolding acc(sl.Bytes(sep, 0, len(sep)), R40) in @ */ sep[0])
		// @ ghost s0 := unfolding acc(sl.Bytes(sep, 0, len(sep)), R40) in sep[0]
		// @ assert View(sep)[0] == s0
		return res
		//gobra:endrewrite e4ce06c882699aa24a46ac5f5ed3a2d1331f7d8c7b2a871c9ffe07721bfb9039
	case n == len(s):
		if Equal(sep, s) {
			return 0
		}
		return -1
	case n > len(s):
		return -1
	case n <= bytealg.MaxLen:
		// Use brute force when s and sep both are small
		if len(s) <= bytealg.MaxBruteForce {
			//gobra:rewrite 995fa64579b51d79f9f879d5f8e3762d24f4fdca91658781b8cae477bd10eba4
			//gobra:cont 			return bytealg.Index(s, sep)
			//gobra:end-old-code 995fa64579b51d79f9f879d5f8e3762d24f4fdca91658781b8cae477bd10eba4
			res = bytealg.Index(s, sep)
			return res
			//gobra:endrewrite 995fa64579b51d79f9f879d5f8e3762d24f4fdca91658781b8cae477bd10eba4
		}
		// @ unfold acc(sl.Bytes(sep, 0, len(sep)), R40)
		c0 := sep[0]
		c1 := sep[1]
		// @ fold acc(sl.Bytes(sep, 0, len(sep)), R40)
		i := 0
		t := len(s) - n + 1
		fails := 0

		// @ invariant acc(sl.Bytes(s, 0, len(s)), R40)
		// @ invariant acc(sl.Bytes(sep, 0, len(sep)), R40)
		// @ invariant c0 == View(sep)[0]
		// @ invariant c1 == View(sep)[1]
		// @ invariant i >= 0
		// @ invariant fails >= 0
		// @ invariant t == len(s) - n + 1
		// @ invariant forall j int :: { View(s)[j:j+len(sep)] } 0 <= j && j < i ==> View(s)[j:j+len(sep)] != View(sep)
		// @ decreases t - i
		for i < t {
			// @ ghost vs := View(s)
			// @ unfold acc(sl.Bytes(s, 0, len(s)), R41)
			if s[i] != c0 {
				// IndexByte is faster than bytealg.Index, so use it as long as
				// we're not getting lots of false positives.
				// @ SubSliceOverlaps(s, i+1, t)
				// @ fold acc(sl.Bytes(s[i+1:t], 0, len(s[i+1:t])), R41)
				o := IndexByte(s[i+1:t], c0)
				// # assert forall j int :: {View(s[i+1:t])[j]} 0 <= j && j < o ==> View(s[i+1:t])[j] != c0
				// @ assume forall j int :: {View(s)[i+1:t][j]} 0 <= j && j < o ==> View(s)[i+1:t][j] != c0

				if o < 0 {
					// @ assert forall j int :: {View(s[i+1:t])[j]} 0 <= j && j < len(s[i+1:t]) ==> View(s[i+1:t])[j] != c0
					// @ assume forall j int :: {View(s)[i+1:t][j]} 0 <= j && j < len(s[i+1:t]) ==> View(s)[i+1:t][j] != c0
					// @ unfold acc(sl.Bytes(s[i+1:t], 0, len(s[i+1:t])), R41)
					// @ fold acc(sl.Bytes(s, 0, len(s)), R41)
					// @ lemmaIndexIndexByteNotFound(View(s), View(sep), i, t)
					return -1
				}
				// @ unfold acc(sl.Bytes(s[i+1:t], 0, len(s[i+1:t])), R41)

				// @ lemmaIndexIndexByteIsNotPrefix(View(s), View(sep), i, t, o)

				i += o + 1
			}
			// @ assert forall j int :: { View(s)[j:j+len(sep)] } 0 <= j && j < i ==> View(s)[j:j+len(sep)] != View(sep)
			// @ fold acc(sl.Bytes(s, 0, len(s)), R41)
			// @ assert acc(sl.Bytes(s, 0, len(s)), R40)

			// @ unfold acc(sl.Bytes(s, 0, len(s)), R41)
			// @ SubSliceOverlaps(s, i, i+n)
			//gobra:rewrite 7bafdf7e4e13158c42c57d2807162d86acab287627cdfddb8689900171421936
			//gobra:cont 			if s[i+1] == c1 && Equal(s[i:i+n], sep) {
			//gobra:end-old-code 7bafdf7e4e13158c42c57d2807162d86acab287627cdfddb8689900171421936
			p1 := s[i+1] == c1
			// @ fold acc(sl.Bytes(s[i:i+n], 0, len(s[i:i+n])), R41)
			if p1 && Equal(s[i:i+n], sep) {
				// @ unfold acc(sl.Bytes(s[i:i+n], 0, len(s[i:i+n])), R41)
				// @ fold acc(sl.Bytes(s, 0, len(s)), R41)
				// @ assert vs == View(s)
				//gobra:endrewrite 7bafdf7e4e13158c42c57d2807162d86acab287627cdfddb8689900171421936
				// @ assert forall j int :: {View(s)[j:j+len(sep)]} 0 <= j && j < i ==> View(s)[j:j+len(sep)] != View(sep)
				// @ assert forall j int :: {View(s)[j:j+len(sep)]} 0 <= j && j < i ==> View(s)[j:j+len(sep)] != View(sep)
				return i
			}
			// @ unfold acc(sl.Bytes(s[i:i+n], 0, len(s[i:i+n])), R41)
			// @ fold acc(sl.Bytes(s, 0, len(s)), R41)
			fails++
			// @ assert forall j int :: { View(s)[j:j+len(sep)] } 0 <= j && j < i ==> View(s)[j:j+len(sep)] != View(sep)
			i++
			// Switch to bytealg.Index when IndexByte produces too many false positives.
			if fails > bytealg.Cutover(i) {
				// @ unfold acc(sl.Bytes(s, 0, len(s)), R41)
				// @ SubSliceOverlaps(s, i, len(s))
				// @ fold acc(sl.Bytes(s[i:], 0, len(s[i:])), R41)
				r := bytealg.Index(s[i:], sep)
				// @ assert r != -1 ==> forall j int :: {View(s[i:])[j:j+len(sep)]} 0 <= j && j < r ==> View(s[i:])[j:j+len(sep)] != View(sep)
				// @ assume r != -1 ==> forall j int :: {View(s)[i:][j:j+len(sep)]} 0 <= j && j < r ==> View(s)[i:][j:j+len(sep)] != View(sep)
				// @ unfold acc(sl.Bytes(s[i:], 0, len(s[i:])), R41)
				// @ fold acc(sl.Bytes(s, 0, len(s)), R41)
				if r >= 0 {

					// @ assert forall j int :: {View(s)[i:][j:j+len(sep)]} 0 <= j && j < r ==> View(s)[i:][j:j+len(sep)] != View(sep)
					// @ assume forall j int :: {View(s)[j:j+len(sep)]} i <= j && j < r+i ==> View(s)[j:j+len(sep)] != View(sep)

					// @ assert forall j int :: { View(s)[j:j+len(sep)] } 0 <= j && j < i ==> View(s)[j:j+len(sep)] != View(sep)
					// # assert forall j int :: { View(s)[j:j+len(sep)] } 0 <= j && j < i ==> View(s)[j:j+len(sep)] != View(sep)
					// @ lemmaIndexAdvance(View(s), View(sep), i, r+i)
					// @ assert forall j int :: {View(s)[j:j+len(sep)]} 0 <= j && j < r+i ==> View(s)[j:j+len(sep)] != View(sep)

					// @ assert r + i != -1

					return r + i
				}
				// @ assert -1 == -1 ==> forall k int :: {View(s)[k:k+len(sep)]} 0 <= k && k + len(sep) <= len(s) ==> View(s)[k:k+len(sep)] != View(sep)
				return -1
			}
		}
		return -1
	}
	// @ unfold acc(sl.Bytes(sep, 0, len(sep)), R41)
	c0 := sep[0]
	c1 := sep[1]
	// @ fold acc(sl.Bytes(sep, 0, len(sep)), R41)
	i := 0
	fails := 0
	t := len(s) - n + 1
	// @ ghost vsep := View(sep)
	// @ ghost vs := View(s)
	// @ invariant acc(sl.Bytes(s, 0, len(s)), R40)
	// @ invariant acc(sl.Bytes(sep, 0, len(sep)), R40)
	// @ invariant vs == View(s)
	// @ invariant vsep == View(sep)
	// @ invariant c0 == vsep[0]
	// @ invariant c1 == vsep[1]
	// @ invariant InRangeInc(i, 0, t)
	// @ invariant t == len(s) - n + 1
	// @ invariant forall j int :: { vs[j:j+len(sep)] } 0 <= j && j < i ==> vs[j:j+len(sep)] != vsep
	// @ decreases t - i
	for i < t {
		// @ unfold acc(sl.Bytes(s, 0, len(s)), R41)
		if s[i] != c0 {
			// @ assert forall j int :: {&s[i+1:t][j]} 0 <= j && j < len(s[i+1:t]) ==> &s[i+1:t][j] == &s[j+i+1]
			// @ fold acc(sl.Bytes(s[i+1:t], 0, len(s[i+1:t])), R41)
			o := IndexByte(s[i+1:t], c0)
			// @ assert View(s[i+1:t]) == vs[i+1:t]
			// @ unfold acc(sl.Bytes(s[i+1:t], 0, len(s[i+1:t])), R41)
			if o < 0 {
				// @ fold acc(sl.Bytes(s, 0, len(s)), R41)
				break
			}
			i += o + 1
		}
		//gobra:rewrite 5e92da7b0d472efdc4e87211ab9ead496a89c44d2219edf05a825aa7b3088140
		//gobra:cont 		if s[i+1] == c1 && Equal(s[i:i+n], sep) {
		//gobra:end-old-code 5e92da7b0d472efdc4e87211ab9ead496a89c44d2219edf05a825aa7b3088140
		p1 := s[i+1] == c1
		// @ assert forall j int :: {&s[i:i+n][j]} 0 <= j && j < len(s[i:i+n]) ==> &s[i:i+n][j] == &s[j+i]
		// @ fold acc(sl.Bytes(s[i:i+n], 0, len(s[i:i+n])), R41)
		if p1 && Equal(s[i:i+n], sep) {
			// @ unfold acc(sl.Bytes(s[i:i+n], 0, len(s[i:i+n])), R41)
			//gobra:endrewrite 5e92da7b0d472efdc4e87211ab9ead496a89c44d2219edf05a825aa7b3088140
			// @ fold acc(sl.Bytes(s, 0, len(s)), R41)
			// @ assert i != -1 ==> forall j int :: {View(s)[j:j+len(sep)]} 0 <= j && j < i ==> View(s)[j:j+len(sep)] != View(sep)
			return i
		}
		// @ unfold acc(sl.Bytes(s[i:i+n], 0, len(s[i:i+n])), R41)
		i++
		fails++
		if fails >= 4+i>>4 && i < t {
			// Give up on IndexByte, it isn't skipping ahead
			// far enough to be better than Rabin-Karp.
			// Experiments (using IndexPeriodic) suggest
			// the cutover is about 16 byte skips.
			// TODO: if large prefixes of sep are matching
			// we should cutover at even larger average skips,
			// because Equal becomes that much more expensive.
			// This code does not take that effect into account.
			// @ assert forall j int :: {&s[i:][j]} 0 <= j && j < len(s[i:]) ==> &s[i:][j] == &s[j+i]
			// @ fold acc(sl.Bytes(s[i:], 0, len(s[i:])), R41)
			j := bytealg.IndexRabinKarpBytes(s[i:], sep)
			// @ unfold acc(sl.Bytes(s[i:], 0, len(s[i:])), R41)
			if j < 0 {
				// @ fold acc(sl.Bytes(s, 0, len(s)), R41)
				return -1
			}
			// @ fold acc(sl.Bytes(s, 0, len(s)), R41)
			// @ assume forall k int :: {View(s)[k:k+len(sep)]} 0 <= k && k < i+j ==> View(s)[k:k+len(sep)] != View(sep)
			return i + j
		}
		// @ fold acc(sl.Bytes(s, 0, len(s)), R41)
	}
	return -1
}

// Cut slices s around the first instance of sep,
// returning the text before and after sep.
// The found result reports whether sep appears in s.
// If sep does not appear in s, cut returns s, nil, false.
//
// Cut returns slices of the original slice s, not copies.
//
// @ preserves acc(sl.Bytes(s, 0, len(s)), R40)
//
// @ preserves acc(sl.Bytes(sep, 0, len(sep)), R40)
//
// @ ensures found ==> len(b) + len(sep) + len(after) == len(s)
// @ ensures found ==> forall i int :: {&s[:len(b)][i]} 0 <= i && i < len(s[:len(b)]) ==> &s[:len(b)][i] == &b[i]
// @ ensures found ==> forall i int :: {&s[len(b)+len(sep):][i]} 0 <= i && i < len(s[len(b)+len(sep):]) ==> &s[len(b)+len(sep):][i] == &after[i]
// @ ensures !found ==> forall i int :: {View(s)[i:i+len(sep)]} 0 <= i && i + len(sep) <= len(s) ==> View(s)[i:i+len(sep)] != View(sep)
// @ ensures !found ==> len(s) == len(b) && (forall i int :: {&s[i]}{&b[i]} 0 <= i && i < len(s) ==> &s[i] == &b[i]) && after == nil
//
// @ decreases
//
//gobra:rewrite e87ea459dcf89b1423be9fd397d8f4767ad24881f1ab27c606aec78e6a86fea4
//gobra:cont func Cut(s, sep []byte) (before, after []byte, found bool) {
//gobra:end-old-code e87ea459dcf89b1423be9fd397d8f4767ad24881f1ab27c606aec78e6a86fea4
func Cut(s, sep []byte) (b, after []byte, found bool) {
	//gobra:endrewrite e87ea459dcf89b1423be9fd397d8f4767ad24881f1ab27c606aec78e6a86fea4
	if i := Index(s, sep); i >= 0 {
		return s[:i], s[i+len(sep):], true
	}
	return s, nil, false
}

// @ preserves acc(sl.Bytes(b, 0, len(b)), R49)
//
// @ ensures sl.Bytes(res, 0, len(res))
//
// @ ensures View(b) == View(res)
//
// @ decreases
func Clone(b []byte) (res []byte) {
	if b == nil {
		// @ fold sl.Bytes(res, 0, len(res))
		return nil
	}
	//gobra:rewrite 18ffdb418b2210b4a8df68df4e19965b13b5beb29702377d3ae2d6ae4fcc6957
	//gobra:cont 	return append( /* @ R50, @ */ []byte{}, b...)
	//gobra:end-old-code 18ffdb418b2210b4a8df68df4e19965b13b5beb29702377d3ae2d6ae4fcc6957
	// @ unfold acc(sl.Bytes(b, 0, len(b)), R50)
	res = append( /* @ R50, @ */ []byte{}, b...)
	// @ fold acc(sl.Bytes(b, 0, len(b)), R50)
	// @ fold sl.Bytes(res, 0, len(res))
	return res
	//gobra:endrewrite 18ffdb418b2210b4a8df68df4e19965b13b5beb29702377d3ae2d6ae4fcc6957
}

// CutPrefix returns s without the provided leading prefix byte slice
// and reports whether it found the prefix.
// If s doesn't start with prefix, CutPrefix returns s, false.
// If prefix is the empty byte slice, CutPrefix returns s, true.
//
// CutPrefix returns slices of the original slice s, not copies.
// @ trusted
func CutPrefix(s, prefix []byte) (after []byte, found bool) {
	if !HasPrefix(s, prefix) {
		return s, false
	}
	return s[len(prefix):], true
}

// CutSuffix returns s without the provided ending suffix byte slice
// and reports whether it found the suffix.
// If s doesn't end with suffix, CutSuffix returns s, false.
// If suffix is the empty byte slice, CutSuffix returns s, true.
//
// CutSuffix returns slices of the original slice s, not copies.
//
// @ trusted
//
//gobra:rewrite 8ffb74d9bb6cd2eea093a78310d9ee0b1bf3464ef13e5e230a4260846c8e2c35
//gobra:cont func CutSuffix(s, suffix []byte) (before []byte, found bool) {
//gobra:end-old-code 8ffb74d9bb6cd2eea093a78310d9ee0b1bf3464ef13e5e230a4260846c8e2c35
func CutSuffix(s, suffix []byte) (b []byte, found bool) {
	//gobra:endrewrite 8ffb74d9bb6cd2eea093a78310d9ee0b1bf3464ef13e5e230a4260846c8e2c35
	if !HasSuffix(s, suffix) {
		return s, false
	}
	return s[:len(s)-len(suffix)], true
}
