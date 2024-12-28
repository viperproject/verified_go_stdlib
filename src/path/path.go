// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package path implements utility routines for manipulating slash-separated
// paths.
//
// The path package should only be used for paths separated by forward
// slashes, such as the paths in URLs. This package does not deal with
// Windows paths with drive letters or backslashes; to manipulate
// operating system paths, use the path/filepath package.
package path

// @ import (
// @	. "verification/utils/definitions"
// @	sl "gobra-libs/byteslice"
// @	seqs "verification/utils/seqs"
// @	sets "verification/utils/sets"
// @	bytes "gobra-libs/bytes"
// @ )

// +gobra

type string_byte = []byte

// A lazybuf is a lazily constructed path buffer.
// It supports append, reading previously appended bytes,
// and retrieving the final string. It does not allocate a buffer
// to hold the output until that output diverges from s.
type lazybuf struct {
	s   string_byte
	buf []byte
	w   int
}

// @ requires acc(Lazybuf(b, R41), R50)
// @ requires InRange(i, 0, len(getS(b)))
// @ ensures acc(Lazybuf(b, R41), R50)
// @ ensures InRange(i, 0, len(getS(b)))
// @ ensures b.specIndex(i) == res
// @ decreases
func (b *lazybuf) index(i int) (res byte) {
	// @ unfold acc(Lazybuf(b, R41), R50)
	// @ defer fold acc(Lazybuf(b, R41), R50)
	if b.buf != nil {
		// @ unfold acc(sl.Bytes(b.buf, 0, len(b.buf)), R45*R50)
		// @ defer fold acc(sl.Bytes(b.buf, 0, len(b.buf)), R45*R50)
		return b.buf[i]
	}
	// @ unfold acc(sl.Bytes(b.s, 0, len(b.s)), R41*R50)
	// @ defer fold acc(sl.Bytes(b.s, 0, len(b.s)), R41*R50)
	return b.s[i]
}

// @ requires Lazybuf(b, R41)
//
// @ requires lazybufInvariant(b)
//
// @ requires getW(b) < len(getS(b))
//
// @ ensures Lazybuf(b, R41)
//
// @ ensures old(getW(b)) + 1 == getW(b)
//
// @ ensures lazybufInvariant(b)
//
// @ ensures old(getS(b)) == getS(b)
//
// @ ensures 1 <= len(getValue(b))
//
// @ ensures lastByte(getValue(b)) == c
//
// @ ensures getValue(b) == old(getValue(b)) ++ seq[byte]{ c }
//
// @ decreases
func (b *lazybuf) append(c byte) {
	// @ unfold Lazybuf(b, R41)
	if b.buf == nil {
		// @ unfold acc(sl.Bytes(b.s, 0, len(b.s)), R45)
		// @ val := b.s[b.w]
		if b.w < len(b.s) && b.s[b.w] == c {
			b.w++
			// @ fold acc(sl.Bytes(b.s, 0, len(b.s)), R45)
			// @ fold Lazybuf(b, R41)
			// @ assert (getS(b)[:getW(b)] == getValue(b)) ==
			// @	unfolding Lazybuf(b, R41) in b.buf == nil
			return
		}
		b.buf = make([]byte, len(b.s))
		// @ SubSliceOverlaps(b.s, 0, b.w)
		copy(b.buf, b.s[:b.w] /* @ , R45 @ */)
		// @ fold acc(sl.Bytes(b.s, 0, len(b.s)), R45)
		// @ fold sl.Bytes(b.buf, 0, len(b.buf))
		// @ fold Lazybuf(b, R41)
		// @ lemmaSlicesIneqLastElem(getS(b)[:getW(b)], getValue(b), val, c)
		// @ unfold Lazybuf(b, R41)
	}
	// @ fold Lazybuf(b, R41)
	// @ ghost w := getW(b)
	// @ ghost oldval := getValue(b)

	// @ requires Lazybuf(b, R41)
	// @ requires getW(b) < len(getS(b))
	// @ requires unfolding Lazybuf(b, R41) in b.buf != nil
	// @ ensures Lazybuf(b, R41)
	// @ ensures getW(b) == before(getW(b)) + 1
	// @ ensures lazybufInvariant(b)
	// @ ensures before(getS(b)) == getS(b)
	// @ ensures lastByte(getValue(b)) == c
	// @ ensures getValue(b) == before(getValue(b)) ++ seq[byte]{ c }
	// @ decreases
	// @ outline (

	// @ unfold Lazybuf(b, R41)
	// @ unfold sl.Bytes(b.buf, 0, len(b.buf))
	b.buf[b.w] = c
	// @ fold sl.Bytes(b.buf, 0, len(b.buf))
	b.w++
	// @ fold Lazybuf(b, R41)
	// @ )
}

// @ requires Lazybuf(b, R41)
// @ ensures acc(sl.Bytes(res, 0, len(res)), R41)
// @ ensures sl.View(res) == old(getValue(b))
//
// @ decreases
func (b *lazybuf) string() (res string_byte) {
	// @ unfold Lazybuf(b, R41)
	if b.buf == nil {
		//gobra:rewrite 55a9058f66d7ec4eb7dcedbcb81150100fed02eb056ec592fa972a8b7c4d282d
		//gobra:cont 		return b.s[:b.w]
		//gobra:end-old-code 55a9058f66d7ec4eb7dcedbcb81150100fed02eb056ec592fa972a8b7c4d282d
		// @ unfold acc(sl.Bytes(b.s, 0, len(b.s)), R41)
		res = b.s[:b.w]
		// @ fold acc(sl.Bytes(res, 0, len(res)), R41)
		return res
		//gobra:endrewrite 55a9058f66d7ec4eb7dcedbcb81150100fed02eb056ec592fa972a8b7c4d282d
	}
	//gobra:rewrite cbf2c42ce1e10c57fe0cb16664da45e809fec83320ddc61ef3bdc35af5e2ddd6
	//gobra:cont 	return string_byte(b.buf[:b.w])
	//gobra:end-old-code cbf2c42ce1e10c57fe0cb16664da45e809fec83320ddc61ef3bdc35af5e2ddd6
	// @ unfold acc(sl.Bytes(b.buf, 0, len(b.buf)), R41)
	res = string_byte(b.buf[:b.w])
	// @ fold acc(sl.Bytes(res, 0, len(res)), R41)
	return res
	//gobra:endrewrite cbf2c42ce1e10c57fe0cb16664da45e809fec83320ddc61ef3bdc35af5e2ddd6
}

// Clean returns the shortest path name equivalent to path
// by purely lexical processing. It applies the following rules
// iteratively until no further processing can be done:
//
//  1. Replace multiple slashes with a single slash.
//  2. Eliminate each . path name element (the current directory).
//  3. Eliminate each inner .. path name element (the parent directory)
//     along with the non-.. element that precedes it.
//  4. Eliminate .. elements that begin a rooted path:
//     that is, replace "/.." by "/" at the beginning of a path.
//
// The returned path ends in a slash only if it is the root "/".
//
// If the result of this process is an empty string, Clean
// returns the string ".".
//
// See also Rob Pike, “Lexical File Names in Plan 9 or
// Getting Dot-Dot Right,”
// https://9p.io/sys/doc/lexnames.html
//
// @ requires acc(sl.Bytes(path, 0, len(path)), R40)
//
// @ ensures acc(sl.Bytes(path, 0, len(path)), R41)
//
// @ ensures acc( sl.Bytes(res, 0, len(res)), R41 )
//
// @ ensures SpecClean(ToPath(sl.View(path))) == ToPath(sl.View(res))
//
// @ decreases
func Clean(path string_byte) (res string_byte) {
	//gobra:rewrite 70493558394bddd26fc4913b3282a2fc8d74fce232cdd1932ae5fad203b0798b
	//gobra:cont 	if path == "" {
	//gobra:cont 		return "."
	//gobra:cont 	}
	//gobra:end-old-code 70493558394bddd26fc4913b3282a2fc8d74fce232cdd1932ae5fad203b0798b
	if len(path) == 0 {
		res = string_byte{'.'}
		// @ fold sl.Bytes(res, 0, len(res))
		// @ lemmaToPathDot(sl.View(res))

		return res
	}
	//gobra:endrewrite 70493558394bddd26fc4913b3282a2fc8d74fce232cdd1932ae5fad203b0798b

	// @ unfold acc(sl.Bytes(path, 0, len(path)), R41)
	rooted := path[0] == '/'
	// @ fold   acc(sl.Bytes(path, 0, len(path)), R41)
	n := len(path)

	// Invariants:
	//	reading from path; r is index of next byte to process.
	//	writing to buf; w is index of next byte to write.
	//	dotdot is index in buf where .. must stop, either because
	//		it is the leading slash or it is a leading ../../.. prefix.
	out /* @@@ */ := lazybuf{s: path}
	// @ fold sl.Bytes(out.buf, 0, len(out.buf))
	// @ fold Lazybuf(&out, R41)
	r, dotdot := 0, 0
	if rooted {
		out.append('/')
		r, dotdot = 1, 1
	}

	// @ invariant InRangeInc(r, 0, n)
	// @ invariant Lazybuf(&out, R41)
	// @ invariant lazybufInvariant(&out)
	// @ invariant dotdotInvariant(dotdot, rooted, getValue(&out))
	// @ invariant getW(&out) <= r
	// @ invariant (rooted ? 1 : 0) <= dotdot
	// @ invariant rooted ==> unfolding Lazybuf(&out, R41) in InRangeInc(out.w, 0, n)
	// @ invariant n == len(getS(&out))
	// @ invariant acc(sl.Bytes(path, 0, len(path)), R41)
	// @ invariant !rooted ==> sl.View(path)[0] != '/'
	// @ invariant rooted ==> 1 <= len(getValue(&out)) && getValue(&out)[0] == '/'
	// @ invariant !rooted && 1 <= len(getValue(&out)) ==> getValue(&out)[0] != '/'
	// @ invariant isCompleted(sl.View(path)[:r]) || willBeCompleted(sl.View(path), r)
	// @ invariant noTrailingSlash(getValue(&out), rooted)
	// @ invariant noDoubleSlash(getValue(&out))
	// @ invariant readingIsAheadOfWriting(sl.View(path), getW(&out), r, rooted)
	// @ invariant SpecClean(ToPath(sl.View(path)[:r] )) == ToPath( getValue(&out) )
	// @ decreases n - r
	for r < n {
		// @ ghost oldR := r
		// @ ghost oldN := n
		// @ ghost measure := n - r
		// @ unfold acc(sl.Bytes(path, 0, len(path)), R45)
		switch {
		case path[r] == '/':
			// empty path element
			r++
			// # assert noIncompleteRead(sl.View(path), r, rooted)
			// @ lemmaToPathAppendingSlash(
			// @	ToPath(sl.View(path)[:r-1] ),
			// @	sl.View(path)[:r-1],
			// @ )
		case path[r] == '.' && (r+1 == n || path[r+1] == '/'):
			// . element
			r++

		case path[r] == '.' && path[r+1] == '.' && (r+2 == n || path[r+2] == '/'):
			// .. element: remove to last /
			r += 2
			// @ unfold Lazybuf(&out, R41)
			switch {
			case out.w > dotdot:
				// can backtrack

				// @ fold Lazybuf(&out, R41)
				// @ ghost prev := getValue(&out)
				// @ ghost origW := getW(&out)
				// @ ghost prevPath := ToPath(getValue(&out))
				// @ lemmaToPathNonEmpty(getValue(&out))
				// @ ghost reducedPath := Path { rooted: prevPath.rooted, parts: prevPath.dirname() }
				// @ ghost ch := lastByte(getValue(&out))
				// @ lemmaNoTrailingSlashPath(getValue(&out), rooted)
				// # assert len(prevPath.basename()) != 0
				// @ unfold Lazybuf(&out, R41)

				out.w--
				// @ fold Lazybuf(&out, R41)

				//gobra:rewrite 30e2737508b727f0d5dfa371555f9b954bf541ea0deccbcda2841807f6db60bb
				//gobra:cont 				for /* @ ( unfolding Lazybuf(&out, R41) in @ */ out.w /* @)@ */ > dotdot && out.index( /* @ unfolding Lazybuf(&out, R41) in @ */ out.w) != '/' {
				//gobra:end-old-code 30e2737508b727f0d5dfa371555f9b954bf541ea0deccbcda2841807f6db60bb
				// see gobra issue #794
				cond := /* @ ( unfolding Lazybuf(&out, R41) in @ */ out.w /* @)@ */ > dotdot && out.index( /* @ unfolding Lazybuf(&out, R41) in @ */ out.w) != '/'
				// @ invariant Lazybuf(&out, R41)
				// @ invariant acc(sl.Bytes(path, 0, len(path)), R50)
				// @ invariant 0 <= dotdot
				// @ invariant r <= n
				// @ invariant n == len(getS(&out))
				// @ invariant getW(&out)+1 <= r
				// @ invariant getW(&out) >= dotdot
				// @ invariant rooted ==> 1 <= len(getValue(&out)) && getValue(&out)[0] == '/'
				// @ invariant lazybufInvariant(&out)

				// @ invariant dotdotInvariant(dotdot, rooted, getValue(&out))
				// @ invariant noDoubleSlash(getValue(&out))
				// @ invariant prev[:origW] == out.valueUntrimmed()[:origW]
				// @ invariant getW(&out) < origW
				// @ invariant len(getValue(&out)) < len(prev)
				// @ invariant cond == (getW(&out) > dotdot && out.specIndex(getW(&out)) != '/')

				// @ invariant readingIsAheadOfWriting(sl.View(path), getW(&out), r, rooted)
				// @ invariant len(ToPath(out.valueUntrimmed()[:getW(&out)+1]).parts) > 0
				// @ invariant ToPath(out.valueUntrimmed()[:getW(&out)+1]).dirname() == reducedPath.parts
				// @ decreases getW(&out)
				for cond {
					//gobra:endrewrite 30e2737508b727f0d5dfa371555f9b954bf541ea0deccbcda2841807f6db60bb
					// @ ghost prev := getValue(&out)
					// @ ghost ch := out.specIndex(getW(&out))
					// @ assert out.valueUntrimmed()[:getW(&out)+1] == prev ++ seq[byte]{ch}
					// @ unfold Lazybuf(&out, R41)
					// @ lemmaLeqTransitive(0, dotdot, out.w - 1)
					out.w--
					// @ fold Lazybuf(&out, R41)
					// @ lemmaToPathPoppingNormalChar(prev, ch)
					//gobra:rewrite 4dc76020bae70577e64b330dca83fdf24f3d7593a0154d8abec6dc63f5897fd9
					//gobra:cont 				}
					//gobra:end-old-code 4dc76020bae70577e64b330dca83fdf24f3d7593a0154d8abec6dc63f5897fd9
					cond = /* @ ( unfolding Lazybuf(&out, R41) in @ */ out.w /* @)@ */ > dotdot && out.index( /* @ unfolding Lazybuf(&out, R41) in @ */ out.w) != '/'
				}
				//gobra:endrewrite 4dc76020bae70577e64b330dca83fdf24f3d7593a0154d8abec6dc63f5897fd9
			/* @

			ghost w := getW(&out)
			ghost if w > dotdot && len(getValue(&out)) != (rooted ? 1 : 0) {
				lemmaNoTrailingSlash(prev, w, rooted)

			}
			@ */
			// @ lemmaToPathAppendingDotdot(
			// @   ToPath(sl.View(path)[:r-2] ),
			// @   sl.View(path)[:r-2],
			// @ )

			// @ unfold Lazybuf(&out, R41)
			case !rooted:
				// cannot backtrack, but not rooted, so append .. element.
				if out.w > 0 {
					// @ fold Lazybuf(&out, R41)
					out.append('/')
					// @ unfold Lazybuf(&out, R41)
				}
				// @ fold Lazybuf(&out, R41)
				out.append('.')
				out.append('.')
				// @ unfold Lazybuf(&out, R41)
				dotdot = out.w
			}
			// @ fold Lazybuf(&out, R41)
		default:
			// real path element.
			// add slash if needed
			// @ unfold Lazybuf(&out, R41)
			if rooted && out.w != 1 || !rooted && out.w != 0 {
				// @ fold Lazybuf(&out, R41)
				out.append('/')
				// @ unfold Lazybuf(&out, R41)
			}
			// @ fold Lazybuf(&out, R41)
			// @ ghost origR := r
			// @ ghost offset := r - getW(&out)
			// copy element
			// @ invariant InRangeInc(r, 0, n)
			// @ invariant Lazybuf(&out, R41)
			// @ invariant getW(&out) <= r
			// @ invariant n == len(getS(&out))
			// @ invariant lazybufInvariant(&out)
			// @ invariant origR <= r
			// @ invariant forall i int :: {&path[i]} 0 <= i && i < len(path) ==> acc(&path[i], R50)
			// @ invariant !(r < n && path[r] != '/') ==> origR < r
			// @ invariant rooted ==> 1 <= len(getValue(&out)) && getValue(&out)[0] == '/'
			// @ invariant r != origR ==> noTrailingSlash(getValue(&out), rooted)
			// @ invariant dotdotInvariant(dotdot, rooted, getValue(&out))
			// @ invariant noDoubleSlash(getValue(&out))
			// @ invariant !rooted && 1 <= len(getValue(&out)) ==> getValue(&out)[0] != '/'
			// @ decreases n - r
			for ; r < n && path[r] != '/'; r++ {
				// @ lemmaLeqTransitive(getW(&out), r, n-1)
				out.append(path[r])
			}

		}
		// @ fold acc(sl.Bytes(path, 0, len(path)), R45)

		// @ assert oldR < r
		// @ assert oldN == n
		// @ assert measure > n - r
	}

	// Turn empty string into "."
	// @ unfold Lazybuf(&out, R41)
	if out.w == 0 {
		//gobra:rewrite 7217a0df192ee4c8dace6a1956998718431158b18202a1c4e6de8921479f6bd3
		//gobra:cont 		return "."
		//gobra:end-old-code 7217a0df192ee4c8dace6a1956998718431158b18202a1c4e6de8921479f6bd3
		res = string_byte{'.'}
		// @ fold acc(sl.Bytes(res, 0, len(res)), R40)
		return res
		//gobra:endrewrite 7217a0df192ee4c8dace6a1956998718431158b18202a1c4e6de8921479f6bd3
	}
	// @ fold Lazybuf(&out, R41)

	//gobra:rewrite f5aa2c6509b2590f5eae382906e321f379502f39d2bd978429ef7b985350ce06
	//gobra:cont 	return out.string()
	//gobra:end-old-code f5aa2c6509b2590f5eae382906e321f379502f39d2bd978429ef7b985350ce06
	res = out.string()
	return res
	//gobra:endrewrite f5aa2c6509b2590f5eae382906e321f379502f39d2bd978429ef7b985350ce06
}

// lastSlash(s) is strings.LastIndex(s, "/") but we can't import strings.
// @ preserves acc(sl.Bytes(s, 0, len(s)), R50)
// @ ensures InRange(res, -1, len(s))
// @ decreases
func lastSlash(s string_byte) (res int) {
	i := len(s) - 1
	// @ unfold acc(sl.Bytes(s, 0, len(s)), R50)
	// @ invariant InRange(i, -1, len(s))
	// @ invariant forall i int :: {&s[i]} 0 <= i && i < len(s) ==> acc(&s[i], R50)
	// @ decreases i
	for i >= 0 && s[i] != '/' {
		i--
	}
	// @ fold acc(sl.Bytes(s, 0, len(s)), R50)
	return i
}

// Split splits path immediately following the final slash,
// separating it into a directory and file name component.
// If there is no slash in path, Split returns an empty dir and
// file set to path.
// The returned values have the property that path = dir+file.
// @ requires acc(sl.Bytes(path, 0, len(path)), R40)
// @ ensures acc(sl.Bytes(path, 0, len(path)), R41)
// @ ensures acc(sl.Bytes(dir, 0, len(dir)), R41)
// @ ensures acc(sl.Bytes(file, 0, len(file)), R41)
// @ decreases
func Split(path string_byte) (dir, file string_byte) {
	i := lastSlash(path)
	//gobra:rewrite 04ab994e84db0990f91b85600e4e43ef0bfd1fd0cabfef3b1c509860ace6cc65
	//gobra:cont 	return path[:i+1], path[i+1:]
	//gobra:end-old-code 04ab994e84db0990f91b85600e4e43ef0bfd1fd0cabfef3b1c509860ace6cc65
	// @ unfold acc(sl.Bytes(path, 0, len(path)), R41)
	// @ SubSliceOverlaps(path, 0, i+1)
	dir = path[:i+1]
	// @ fold acc(sl.Bytes(dir, 0, len(dir)), R41)
	// @ SubSliceOverlaps(path, i+1, len(path))
	file = path[i+1:]
	// @ fold acc(sl.Bytes(file, 0, len(file)), R41)
	return dir, file
	//gobra:endrewrite 04ab994e84db0990f91b85600e4e43ef0bfd1fd0cabfef3b1c509860ace6cc65
}

// Join joins any number of path elements into a single path,
// separating them with slashes. Empty elements are ignored.
// The result is Cleaned. However, if the argument list is
// empty or all its elements are empty, Join returns
// an empty string.
//
// @ requires false
// @ trusted
func Join(elem []string_byte) string_byte {
	size := 0
	for _, e := range elem {
		size += len(e)
	}
	if size == 0 {
		return string_byte{}
	}
	buf := make([]byte, 0, size+len(elem)-1)
	for _, e := range elem {
		//gobra:rewrite 88352fa84dd71f512688eb2be16383939fc26545c129deb8462fd5178583bdff
		//gobra:cont 		if len(buf) > 0 || e != "" {
		//gobra:end-old-code 88352fa84dd71f512688eb2be16383939fc26545c129deb8462fd5178583bdff
		if len(buf) > 0 || len(e) != 0 {
			//gobra:endrewrite 88352fa84dd71f512688eb2be16383939fc26545c129deb8462fd5178583bdff
			if len(buf) > 0 {
				buf = append( /* @ R40 , @ */ buf, '/')
			}
			buf = append( /* @ R40, @ */ buf, e...)
		}
	}
	return Clean(string_byte(buf))
}

// Ext returns the file name extension used by path.
// The extension is the suffix beginning at the final dot
// in the final slash-separated element of path;
// it is empty if there is no dot.
//
// @ requires false
// @ trusted
func Ext(path string_byte) string_byte {
	for i := len(path) - 1; i >= 0 && path[i] != '/'; i-- {
		if path[i] == '.' {
			return path[i:]
		}
	}
	return string_byte{}
}

// Base returns the last element of path.
// Trailing slashes are removed before extracting the last element.
// If the path is empty, Base returns ".".
// If the path consists entirely of slashes, Base returns "/".
//
// @ requires false
// @ trusted
func Base(path string_byte) string_byte {
	//gobra:rewrite 70493558394bddd26fc4913b3282a2fc8d74fce232cdd1932ae5fad203b0798b
	//gobra:cont 	if path == "" {
	//gobra:cont 		return "."
	//gobra:cont 	}
	//gobra:end-old-code 70493558394bddd26fc4913b3282a2fc8d74fce232cdd1932ae5fad203b0798b
	if len(path) == 0 {
		return string_byte{'.'}
	}
	//gobra:endrewrite 70493558394bddd26fc4913b3282a2fc8d74fce232cdd1932ae5fad203b0798b
	// Strip trailing slashes.
	for len(path) > 0 && path[len(path)-1] == '/' {
		path = path[0 : len(path)-1]
	}
	// Find the last element
	if i := lastSlash(path); i >= 0 {
		path = path[i+1:]
	}
	// If empty now, it had only slashes.
	if len(path) == 0 {
		return string_byte{'/'}
	}
	return path
}

// IsAbs reports whether the path is absolute.
//
// @ preserves acc(sl.Bytes(path, 0, len(path)), R50)
//
// @ ensures res == ToPath(sl.View(path)).IsAbs()
//
// @ decreases
func IsAbs(path string_byte) (res bool) {
	// @ unfold acc(sl.Bytes(path, 0, len(path)), R50)
	// @ defer fold acc(sl.Bytes(path, 0, len(path)), R50)
	return len(path) > 0 && path[0] == '/'
}

// Dir returns all but the last element of path, typically the path's directory.
// After dropping the final element using Split, the path is Cleaned and trailing
// slashes are removed.
// If the path is empty, Dir returns ".".
// If the path consists entirely of slashes followed by non-slash bytes, Dir
// returns a single slash. In any other case, the returned path does not end in a
// slash.
//
// @ requires false
// @ trusted
func Dir(path string_byte) string_byte {
	dir, _ := Split(path)
	return Clean(dir)
}
