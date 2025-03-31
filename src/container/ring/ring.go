// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package ring implements operations on circular lists.

// +gobra
package ring

// A Ring is an element of a circular list, or ring.
// Rings do not have a beginning or end; a pointer to any ring element
// serves as reference to the entire ring. Empty rings are represented
// as nil Ring pointers. The zero value for a Ring is a one-element
// ring with a nil Value.
type Ring struct {
	next, prev *Ring
	Value      any // for use by client; untouched by this library
}

//@ requires r.Mem(elems, isInit)
//@ ensures  r.Mem(set[*Ring]{r}, true)
//@ ensures  r == res
//@ decreases
func (r *Ring) init(/*@ ghost elems set[*Ring], ghost isInit bool @*/) (res *Ring) {
	//@ unfold r.Mem(elems, isInit)
	r.next = r
	r.prev = r
	//@ fold r.Mem(set[*Ring]{r}, true)
	return r
}

// Next returns the next ring element. r must not be empty.
//# We use 'owner' here to make calls from different receivers in the same ring structure work (see e.g. Link)
//@ requires r != nil
//@ requires owner != r ==> r in elems
//@ requires !isInit ==> owner.Mem(elems, false)
//@ requires isInit ==> acc(owner.Mem(elems, true), ReadPerm)
//@ ensures  !isInit ==> (owner.Mem(set[*Ring]{r}, true) && res == r)
//@ ensures  isInit ==> (acc(owner.Mem(elems, true), ReadPerm) && res in elems)
//@ ensures  isInit ==> unfolding acc(owner.Mem(elems, true), ReadPerm) in res == r.next
//@ decreases
func (r *Ring) Next(/*@ ghost elems set[*Ring], ghost owner *Ring, ghost isInit bool @*/) (res *Ring) {
	/*@ 
	ghost if isInit {
		unfold acc(owner.Mem(elems, true), ReadPerm)
	} else {
		unfold owner.Mem(elems, false)
	}
	@*/
	if r.next == nil {
		//@ assert !isInit //# here we know !isInit
		//@ fold owner.Mem(elems, false)
		return r.init(/*@ elems, false @*/)
	}
	res = r.next
	//@ fold acc(owner.Mem(elems, true), ReadPerm)
}

// Prev returns the previous ring element. r must not be empty.
//# We use 'owner' here to make calls from different receivers in the same ring structure work (see e.g. Link)
//@ requires r != nil
//@ requires owner != r ==> r in elems
//@ requires !isInit ==> owner.Mem(elems, false)
//@ requires isInit ==> acc(owner.Mem(elems, true), ReadPerm)
//@ ensures  !isInit ==> (owner.Mem(set[*Ring]{r}, true) && res == r)
//@ ensures  isInit ==> (acc(owner.Mem(elems, true), ReadPerm) && res in elems)
//@ ensures  isInit ==> unfolding acc(owner.Mem(elems, true), ReadPerm) in res == r.prev
//@ decreases
func (r *Ring) Prev( /*@ ghost elems set[*Ring], ghost owner *Ring, ghost isInit bool @*/) (res *Ring) {
	/*@ 
	ghost if isInit {
		unfold acc(owner.Mem(elems, true), ReadPerm)
	} else {
		unfold owner.Mem(elems, false)
	}
	@*/
	if r.next == nil {
		//@ assert !isInit //# here we know !isInit
		//@ fold owner.Mem(elems, false)
		return r.init(/*@ elems, false @*/)
	}
	res = r.prev
	//@ fold acc(owner.Mem(elems, true), ReadPerm)
}

//# Functional properties of this method have NOT yet been verified.
// Move moves n % r.Len() elements backward (n < 0) or forward (n >= 0)
// in the ring and returns that ring element. r must not be empty.
//@ requires  r.Mem(elems, isInit) //# make this PRESERVES
//@ ensures   !isInit ==> (r.Mem(set[*Ring]{r}, true) && res == r)
//@ ensures   n == 0 ==> res == r
//@ ensures   isInit ==> r.Mem(elems, true)
//@ decreases
func (r *Ring) Move(n int /*@, ghost elems set[*Ring], ghost isInit bool @*/) (res *Ring) {
	if /*@ unfolding r.Mem( elems, isInit) in @*/ r.next == nil {
		return r.init(/*@ elems, isInit @*/)
		//@ assert r.Mem(set[*Ring]{r}, true)
	}
	//@ ghost startRing := r  //# included for invariant
    //@ ghost startN := n     //# included for invariant
	switch {
	case n < 0:
		//@ invariant startRing.Mem(elems, true)
		//@ invariant r in elems
		//@ invariant startN <= n && n <= 0
		//@ decreases 0 - n
		for ; n < 0; n++ {
			//@ unfold startRing.Mem(elems, true)
			r = r.prev
			//@ fold startRing.Mem(elems, true)
		}
	case n > 0:
		//@ invariant startRing.Mem(elems, true)
		//@ invariant r in elems
		//@ invariant 0 <= n && n <= startN
		//@ decreases n
		for ; n > 0; n-- {
			//@ unfold startRing.Mem(elems, true)
			r = r.next
			//@ fold startRing.Mem(elems, true)
		}
	}
	return r
}

//# This underlying implementation of 'New' had to be substantially changed in order to verify the loop.
//# The original implementation started with an ring element 'r', attached new ring elements in the loop
//# and closed the ring structure at the very end of the method.
//# This posed challenges in establishing all the required facts for folding the predicate in the very end.
//# This adapted implementation preserves a clean ring structure between iterations where new ring elements get inserted.
//# This adapted implementation passes all tests in 'ring_test.go' and 'example_test.go'.
// New creates a ring of n elements.
//@ ensures n <= 0 ==> res == nil
//@ ensures n > 0 ==> (len(elems) == n && res.Mem(elems, true))
func New(n int) (res *Ring /*@, ghost elems set[*Ring] @*/) {
	if n <= 0 {
		res = nil
		//@ elems = set[*Ring]{}
		return
	}
	r := new(Ring)
	p := r

	//# Changed the implementation to already form a cycle here so that we can use
	//# the memory predicate in the invariant and have an easier time establishing it in the end.
	r.next = r
	r.prev = r
	//@ elems = set[*Ring]{r}
	//@ fold r.Mem(elems, true)
	
	//@ invariant r.Mem(elems, true)
	//@ invariant len(elems) == i
	//@ invariant p in elems
	//@ invariant 1 <= i && i <= n
	//@ decreases n - i
	for i := 1; i < n; i++ {
		//# Implementation was changed. Every iteration we take a consistent ring and return a consistent ring with a new element.
		//@ unfold r.Mem(elems, true)
		q := &Ring{}
		q.prev = p
		q.next = p.next
		q.prev.next = q
		q.next.prev = q
		p = q
		//@ elems = elems union set[*Ring]{p}
		//@ fold r.Mem(elems, true)
	}
	res = r
}

// Link connects ring r with ring s such that r.Next()
// becomes s and returns the original value for r.Next().
// r must not be empty.
//
// If r and s point to the same ring, linking
// them removes the elements between r and s from the ring.
// The removed elements form a subring and the result is a
// reference to that subring (if no elements were removed,
// the result is still the original value for r.Next(),
// and not nil).
//
// If r and s point to different rings, linking
// them creates a single ring with the elements of s inserted
// after r. The result points to the element following the
// last element of s after insertion.
//@ requires r != nil
//@ requires r.Mem(elemsR, true)
//@ requires (s != nil && !(s in elemsR)) ==> s.Mem(elemsS, true)
//@ requires (s != nil && !(s in elemsR)) ==> (elemsR intersection elemsS) == set[*Ring]{}
//@ requires (s != nil && s in elemsR) ==> elemsR == elemsS
//@ ensures  res == old(unfolding r.Mem(elemsR, true) in r.next)
//@ ensures  (s != nil && !(s in elemsR)) ==> res.Mem((elemsR union elemsS), true)
//@ ensures  (s != nil && s in elemsR && r == s && len(elemsR) == 1) ==> res.Mem((elemsR), true)
//# ensures  (s != nil && s in elemsR && r == s && len(elemsR) > 1) ==> res.Mem((elemsR setminus (set[*Ring]{r})), true) UNIMPLEMENTED
//# ensures  (s != nil && s in elemsR && r != s && len(elemsR) == 1) ==> UNIMPLEMENTED
//@ decreases
func (r *Ring) Link(s *Ring /*@, ghost elemsR set[*Ring], ghost elemsS set[*Ring] @*/) (res *Ring) {
	n := r.Next(/*@ elemsR, r, true @*/)
	if s != nil {
		//@ ghost elemsX := (s in elemsR)?(elemsR):(elemsS)
		//@ ghost owner := (s in elemsR)?(r):(s)
		p := s.Prev(/*@ elemsX, owner, true @*/)

        //@ unfold r.Mem(elemsR, true)
		/*@ 
        ghost if !(s in elemsR) {
            unfold s.Mem(elemsS, true)
        }
		@*/
		// Note: Cannot use multiple assignment because
		// evaluation order of LHS is not specified.
		r.next = s
		s.prev = r
		n.prev = p
		p.next = n
		/*@
		ghost if !(s in elemsR){
			//# In this case r and s are from different ring structures. The rings get linked together forming a larger ring containing both elemsS and elemsR.
			fold n.Mem((elemsR union elemsS), true)
		} else {
			ghost if r == s {
				ghost if len(elemsR) == 1 {
					//# In this case r == s formed a ring structure of 1 element and this same structure is returned.
					fold n.Mem(elemsR, true)
				}
				ghost if len(elemsR) > 1 {
					//# UNIMPLEMENTED
					//# In this case r == s formed a ring structure also containing other elements.
					//# We want to prove n.Mem((elemsR setminus (set[*Ring]{r})), true).
					//# This is not possible with the current abstraction because it could be that n == r.
				}
			} else {
				//# UNIMPLEMENTED
				//# In these cases r and s are part of the same ring structure but r != s
			}
		}
		@*/
	}
	return n
}

//# This method could not yet be specified and verified due to the following reasons:
//#		- We do not yet have a spec for 'Move' that talks about its return type
//#		- Only a subset of the different cases of 'Link' could be verified and the relevant cases where n > 0 are not among them.
//#		- 'Move' changes 'r' itself which makes us loose the reference to the Mem predicate.
//#		  One would need to carry the 'owner' construct through the whole call stack to alleviate this issue.
// Unlink removes n % r.Len() elements from the ring r, starting
// at r.Next(). If n % r.Len() == 0, r remains unchanged.
// The result is the removed subring. r must not be empty.
//@ requires false //# UNIMPLEMENTED
//@ requires r != nil
//@ requires r.Mem(elems, isInit)
//@ ensures  n <= 0 ==> res == nil
func (r *Ring) Unlink(n int /*@, ghost elems set[*Ring], ghost owner *Ring, ghost isInit bool @*/) (res *Ring) {
	if n <= 0 {
		return nil
	}
	return r.Link(r.Move(n + 1 /*@, elems, isInit @*/) /*@, elems, elems @*/)
}

// Len computes the number of elements in ring r.
// It executes in time proportional to the number of elements.
//# This method can be called on a ring r that is not yet properly initialized.
//# In that case the loop initialization will call r.Next(), return an initialized ring r and terminate while returning a length of 1.
//@ requires false //# Were unable to verify this method.
//@ requires r != nil ==> (r.Mem(elems, isInit))
//@ ensures  r == nil ==> res == 0
//@ ensures  (r != nil && !isInit) ==> (r.Mem(set[*Ring]{r}, true) && res == 1)
//@ ensures  (r != nil && isInit)  ==> (r.Mem(elems, true) && res == len(elems))
func (r *Ring) Len(/*@ ghost elems set[*Ring], ghost isInit bool @*/) (res int) {
	n := 0
	if r != nil {
		n = 1
        //# There is difficulty in deriving the loop (in)variant.
        //# It could not be established that after len(elems) iterations,
        //# i.e. updating p with p.next, we get to a point where p==r.
		//@ invariant 1 <= n && n <= len(elems)
		//@ invariant !isInit ==> r.Mem(set[*Ring]{r}, true)
		//@ invariant isInit ==> r.Mem(elems, true)
		//@ invariant isInit ==> (r in elems && p in elems)
		//@ invariant !isInit ==> r == p
		//@ decreases len(elems) - n
		for p := r.Next(/*@ elems, r, isInit @*/); p != r; p = ( /*@ unfolding r.Mem(elems, true) in @*/ p.next) {
			n++
		}
	}
	return n
}

// Do calls function f on each element of the ring, in forward order.
// The behavior of Do is undefined if f changes *r.
//@ requires false //# UNIMPLEMENTED
//@ requires r != nil ==> r.Mem(elems, isInit)
//@ trusted //# required because of error with 'f'
func (r *Ring) Do(f func(any) /*@, ghost elems set[*Ring], ghost isInit bool @*/) {
	if r != nil {
		f(r.Value)
		for p := r.Next(/*@ elems, r, isInit @*/); p != r; p = p.next {
			f(p.Value)
		}
	}
}