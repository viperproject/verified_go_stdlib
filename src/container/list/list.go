// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package list implements a doubly linked list.
//
// To iterate over a list (where l is a *List):
//
//	for e := l.Front(); e != nil; e = e.Next() {
//		// do something with e.Value
//	}

// +gobra

package list

// Element is an element of a linked list.
type Element struct {
	// Next and previous pointers in the doubly-linked list of elements.
	// To simplify the implementation, internally a list l is implemented
	// as a ring, such that &l.root is both the next element of the last
	// list element (l.Back()) and the previous element of the first list
	// element (l.Front()).
	next, prev *Element

	// The list to which this element belongs.
	list *List

	// The value stored with this element.
	Value any
}

// Next returns the next list element or nil.
//@ preserves list.Mem(elems, true)
//@ requires  e != &list.root
//@ requires  e in elems //# Via the predicate, this already implies that e.list==nil cannot happen
//@ ensures   unfolding list.Mem(elems, true) in (e.next == &e.list.root) ==> res == nil
//@ ensures   unfolding list.Mem(elems, true) in (e.next != &e.list.root) ==> (res == e.next && res != nil && res != &list.root)
//@ decreases
func (e *Element) Next(/*@ ghost elems set[*Element], ghost list *List @*/) (res *Element) {
	//@ unfold list.Mem(elems, true)
	//@ defer fold list.Mem(elems, true)
	if p := e.next; e.list != nil && p != &e.list.root {
		return p
	}
	return nil
}

// Prev returns the previous list element or nil.
//@ preserves list.Mem(elems, true)
//@ requires  e != &list.root
//@ requires  e in elems //# Via the predicate, this already implies that e.list==nil cannot happen
//@ ensures   unfolding list.Mem(elems, true) in (e.prev == &e.list.root) ==> res == nil
//@ ensures   unfolding list.Mem(elems, true) in (e.prev != &e.list.root) ==> (res == e.prev && res != nil && res != &list.root)
//@ decreases
func (e *Element) Prev(/*@ ghost elems set[*Element], ghost list *List @*/) (res *Element) {
	//@ unfold list.Mem(elems, true)
	//@ defer fold list.Mem(elems, true)
	if p := e.prev; e.list != nil && p != &e.list.root {
		return p
	}
	return nil
}

// List represents a doubly linked list.
// The zero value for List is an empty list ready to use.
type List struct {
	root Element // sentinel list element, only &root, root.prev, and root.next are used
	lenT int     // current list length excluding (this) sentinel element
	//# The original implementation used 'len' as a field name. This was changed to 'lenT' because 'len' serves as a keyword in Gobra, see https://github.com/viperproject/gobra/issues/118
}


// Init initializes or clears list l.
//@ requires l.Mem(elems, isInit)
//@ ensures  res == l
//@ ensures  l.Mem(set[*Element]{&l.root}, true)
//@ ensures  isInit ==> (forall i *Element :: {i in elems} (i in elems && i != &l.root) ==> (acc(&i.next) && acc(&i.prev) && acc(&i.list) && acc(&i.Value)))
//@ ensures  l.Len(set[*Element]{&l.root}, true) == 0
//@ decreases
func (l *List) Init(/*@ ghost elems set[*Element], ghost isInit bool @*/) (res *List) {
	//@ unfold l.Mem(elems, isInit)
	l.root.next = &l.root
	l.root.prev = &l.root
	l.lenT = 0
	//@ fold l.Mem(set[*Element]{&l.root}, true)
	return l
}

// New returns an initialized list.
//@ ensures l.Mem(set[*Element]{&l.root}, true)
//@ ensures l.Len(set[*Element]{&l.root}, true) == 0
//@ decreases
func New() (l *List) {
	l = new(List)
	//@ fold l.Mem(set[*Element]{&l.root}, false)
	l.Init(/*@ set[*Element]{&l.root}, false @*/)
}

// Len returns the number of elements of list l.
// The complexity is O(1).
//@ requires acc(l.Mem(elems, isInit), ReadPerm)
//@ ensures  unfolding acc(l.Mem(elems, isInit), ReadPerm) in res == l.lenT
//@ ensures  unfolding acc(l.Mem(elems, isInit), ReadPerm) in !isInit ==> res == 0
//@ decreases
//@ pure
func (l *List) Len(/*@ ghost elems set[*Element], isInit bool @*/) (res int) {
	return /*@ unfolding acc(l.Mem(elems, isInit), ReadPerm) in @*/ l.lenT
}

// Front returns the first element of list l or nil if the list is empty.
//@ preserves acc(l.Mem(elems, true), ReadPerm)
//@ ensures   l.Len(elems, true) == 0 ==> res == nil
//@ ensures   l.Len(elems, true) != 0 ==> res == (unfolding acc(l.Mem(elems, true), ReadPerm) in l.root.next)
//@ decreases
func (l *List) Front(/*@ ghost elems set[*Element] @*/) (res *Element) {
	//@ unfold acc(l.Mem(elems, true), ReadPerm)
	//@ defer fold acc(l.Mem(elems, true), ReadPerm)
	if l.lenT == 0 {
		return nil
	}
	return l.root.next
}

// Back returns the last element of list l or nil if the list is empty.
//@ preserves acc(l.Mem(elems, true), ReadPerm)
//@ ensures   l.Len(elems, true) == 0 ==> res == nil
//@ ensures   l.Len(elems, true) != 0 ==> res == (unfolding acc(l.Mem(elems, true), ReadPerm) in l.root.prev)
//@ decreases
func (l *List) Back(/*@ ghost elems set[*Element] @*/) (res *Element) {
	//@ unfold acc(l.Mem(elems, true), ReadPerm)
	//@ defer fold acc(l.Mem(elems, true), ReadPerm)
	if l.lenT == 0 {
		return nil
	}
	return l.root.prev
}

// lazyInit lazily initializes a zero List value.
//@ requires l.Mem(elems, isInit)
//@ ensures  l.Mem(elems, true)
//@ ensures  l.Len(elems, true) == old(l.Len(elems, isInit))
//@ decreases
func (l *List) lazyInit(/*@ ghost elems set[*Element], ghost isInit bool @*/) {
	//@ unfold l.Mem(elems, isInit)
	if l.root.next == nil {
		//@ assert !isInit
		//@ fold l.Mem(elems, isInit)
		l.Init(/*@ elems, false @*/)
	}
	/*@
	ghost if isInit {
		fold l.Mem(elems, true)
	}
	@*/
}

// insert inserts e after at, increments l.lenT, and returns e.
//@ requires l.Mem(elems, true)
//@ requires acc(e)
//@ requires at in elems
//@ requires !(e in elems)
//@ ensures  l.Mem(elems union set[*Element]{e}, true)
//@ ensures  l.Len(elems union set[*Element]{e}, true) == 1 + old(l.Len(elems, true))
//@ ensures  at.comesBefore(e, elems union set[*Element]{e}, l)
//@ ensures  e.comesBefore(old(at.nextPure(elems, l)), elems union set[*Element]{e}, l)
//@ ensures  res == e && res != nil && res != &l.root
//@ decreases
func (l *List) insert(e, at *Element /*@, ghost elems set[*Element] @*/) (res *Element) {
	//@ unfold l.Mem(elems, true)
	e.prev = at
	e.next = at.next
	e.prev.next = e
	e.next.prev = e
	e.list = l
	l.lenT++
	//@ fold l.Mem(elems union set[*Element]{e}, true)
	return e
}

// insertValue is a convenience wrapper for insert(&Element{Value: v}, at).
//@ requires l.Mem(elems, true)
//@ requires at in elems
//@ ensures  l.Mem(elems union set[*Element]{res}, true)
//@ ensures  l.Len(elems union set[*Element]{res}, true) == 1 + old(l.Len(elems, true))
//@ ensures  at.comesBefore(res, elems union set[*Element]{res}, l)
//@ ensures  res.comesBefore(old(at.nextPure(elems, l)), elems union set[*Element]{res}, l)
//@ ensures  res != nil && res != &l.root
//@ decreases
func (l *List) insertValue(v any, at *Element /*@, ghost elems set[*Element] @*/) (res *Element) {
	res = &Element{Value: v}
	//@ assert unfolding l.Mem(elems, true) in !(res in elems)
	//# The above assertion serves a trigger for the precondition of 'insert'
	return l.insert(res, at /*@, elems @*/)
}

//@ requires l.Mem(elems, true)
//@ requires e in elems
//@ requires e != &l.root
//@ ensures  l.Mem((elems setminus (set[*Element]{e})), true)
//@ ensures  l.Len((elems setminus (set[*Element]{e})), true) == old(l.Len(elems, true)) - 1
//@ ensures  acc(e) && e.list == nil
//@ decreases
func (l *List) remove(e *Element /*@, ghost elems set[*Element] @*/) {
	//@ unfold l.Mem(elems, true)
	e.prev.next = e.next
	e.next.prev = e.prev
	e.next = nil // avoid memory leaks
	e.prev = nil // avoid memory leaks
	e.list = nil
	l.lenT--
	//@ fold l.Mem((elems setminus (set[*Element]{e})), true)
}

// move moves e to next to at.
//@ requires l.Mem(elems, true)
//@ requires e in elems
//@ requires at in elems
//@ ensures  l.Mem(elems, true)
//@ ensures  (e != at ==> (unfolding l.Mem(elems, true) in (at.next == e && e.prev == at)))
//@ ensures  (e != at && old(at.nextPure(elems, l) != e)) ==> at.comesBefore(e, elems, l)
//@ ensures  (e != at && old(at.nextPure(elems, l) != e)) ==> e.comesBefore(old(at.nextPure(elems, l)), elems, l)
//@ decreases
func (l *List) move(e, at *Element /*@, ghost elems set[*Element] @*/) {
	if e == at {
		return
	}

	//@ unfold l.Mem(elems, true)
	//# remove e
	e.prev.next = e.next
	e.next.prev = e.prev

	//# insert e after at
	e.prev = at
	e.next = at.next
	e.prev.next = e
	e.next.prev = e
	//@ fold l.Mem(elems, true)
}

//### EXPLANATION IFF ###//
//# The developers included a comment in the implementation that explains how it is required for the list to have been initialized if 'e.list==l'.
//# If 'l' were not initialized then the call to 'l.remove(e)' could result in a crash.
//# We know from the predicate that in an initialized list 'l' if 'e in elems' then 'e.list == l".
//# We further want to establish that if 'e.list == l' then 'e in elems', i.e. we want to establish (e.list == l) IFF (e in elems).
//# This helps us to establish that we have permissions to the fields of 'e' via the predicate from the knowledge gathered in the control flow.
//# However, if '!(e in elems)' then we wouldn't have permissions to even check 'e.list == l'.
//# We therefore need an additional precondition 'requires !(e in elems) ==> acc(e)' to be guaranteed to have permissions to 'e.list' exactly once.
//# With 'requires unfolding l.Mem(elems, true) in (e.list == l) == (e in elems)' we can then establish the required equivalence.
//# The 'unfolding' in this line only has an effect on the permissions of 'e.list' if we had 'e in elems'.
//# Otherwise, the permission to 'e.list' come from the precondition 'requires !(e in elems) ==> acc(e)'.
// Remove removes e from l if e is an element of list l.
// It returns the element value e.Value.
// The element must not be nil.
//@ requires e != nil
//@ requires l.Mem(elems, true)
//@ requires e != &l.root
//# The next two lines aim to establish: (e.list == l) IFF (e in elems)
//@ requires !(e in elems) ==> (acc(e) && e.list != l)
//@ requires unfolding l.Mem(elems, true) in (e.list == l) == (e in elems)
//@ ensures  !(e in elems) ==> l.Mem(elems, true)
//@ ensures  e in elems ==> l.Mem((elems setminus (set[*Element]{e})), true)
//@ ensures  acc(e) && e.Value === res && (e in elems ==> e.list == nil)
//@ decreases
func (l *List) Remove(e *Element /*@, ghost elems set[*Element] @*/) (res any) {
	/*@
	ghost if e in elems{
		unfold l.Mem(elems, true)
	}
	@*/
	if e.list == l {
		// if e.list == l, l must have been initialized when e was inserted
		// in l or l == nil (e is a zero Element) and l.remove will crash
		//@ fold l.Mem(elems, true)
		l.remove(e /*@, elems @*/)
	}
	return e.Value
}

// PushFront inserts a new element e with value v at the front of list l and returns e.
//@ requires l.Mem(elems, isInit)
//@ requires &l.root in elems //# This is given by the predicate but explicitly necessary for the postcondition to work without unfolding
//@ ensures  l.Mem(elems union set[*Element]{res}, true)
//@ ensures  l.Len(elems union set[*Element]{res}, true) == 1 + old(l.Len(elems, isInit))
//@ ensures  l.root.comesBefore(res, elems union set[*Element]{res}, l)
//@ ensures  res != nil && res != &l.root
//@ decreases
func (l *List) PushFront(v any /*@, ghost elems set[*Element], ghost isInit bool @*/) (res *Element) {
	l.lazyInit(/*@ elems, isInit @*/)
	//@ assert unfolding l.Mem(elems, true) in &l.root in elems //# Without this explicit unfolding of the Mem predicate the verifier cannot establish that &l.root in elems for the precondition of insertValue
	return l.insertValue(v, &l.root /*@, elems @*/)
}

// PushBack inserts a new element e with value v at the back of list l and returns e.
//@ requires l.Mem(elems, isInit)
//@ requires &l.root in elems //# This is given by the predicate but explicitly necessary for the postcondition to work without unfolding
//@ ensures  l.Mem(elems union set[*Element]{res}, true)
//@ ensures  l.Len(elems union set[*Element]{res}, true) == 1 + old(l.Len(elems, isInit))
//@ ensures  res.comesBefore(&l.root, elems union set[*Element]{res}, l)
//@ ensures  res != nil && res != &l.root
//@ decreases
func (l *List) PushBack(v any /*@, ghost elems set[*Element], ghost isInit bool @*/) (res *Element) {
	l.lazyInit(/*@ elems, isInit @*/)
	return l.insertValue(v, /*@ unfolding l.Mem(elems, true) in @*/ l.root.prev /*@, elems @*/)
}

// InsertBefore inserts a new element e with value v immediately before mark and returns e.
// If mark is not an element of l, the list is not modified.
// The mark must not be nil.
//@ requires mark != nil
//@ requires mark != &l.root
//@ requires l.Mem(elems, true) //# Same as 'Remove', we only accept initialized lists and disallow the crash.
//# The next two lines aim to establish: (mark.list == l) IFF (mark in elems), see top comment in 'Remove' for detailed explanation
//@ requires !(mark in elems) ==> (acc(mark) && mark.list != l)
//@ requires unfolding l.Mem(elems, true) in (mark.list == l) == (mark in elems)
//@ ensures  (mark in elems) ==> l.Mem(elems union set[*Element]{res}, true)
//@ ensures  !(mark in elems) ==> l.Mem(elems, true)
//@ ensures  (mark in elems) ==> res.comesBefore(mark, elems union set[*Element]{res}, l)
//@ ensures  (mark in elems) ==> old(mark.prevPure(elems, l)).comesBefore(res, elems union set[*Element]{res}, l)
//@ ensures  (mark in elems) ==> res != nil && res != &l.root
//@ decreases
func (l *List) InsertBefore(v any, mark *Element /*@, ghost elems set[*Element] @*/) (res *Element) {
	//@ unfold l.Mem(elems, true)
	if mark.list != l {
		//@ fold l.Mem(elems, true)
		return nil
	}
	//@ fold l.Mem(elems, true)
	// see comment in List.Remove about initialization of l
	return l.insertValue(v, /*@ unfolding l.Mem(elems, true) in @*/ mark.prev /*@, elems @*/)
}

// InsertAfter inserts a new element e with value v immediately after mark and returns e.
// If mark is not an element of l, the list is not modified.
// The mark must not be nil.
//@ requires mark != nil
//@ requires mark != &l.root
//@ requires l.Mem(elems, true) //# Same as 'Remove', we only accept initialized lists and disallow the crash.
//# The next two lines aim to establish: (mark.list == l) IFF (mark in elems), see top comment in 'Remove' for detailed explanation
//@ requires !(mark in elems) ==> (acc(mark) && mark.list != l)
//@ requires unfolding l.Mem(elems, true) in (mark.list == l) == (mark in elems)
//@ ensures  (mark in elems) ==> l.Mem(elems union set[*Element]{res}, true)
//@ ensures  !(mark in elems) ==> l.Mem(elems, true)
//@ ensures  (mark in elems) ==> mark.comesBefore(res, elems union set[*Element]{res}, l)
//@ ensures  (mark in elems) ==> res.comesBefore(old(mark.nextPure(elems, l)), elems union set[*Element]{res}, l)
//@ ensures  (mark in elems) ==> res != nil && res != &l.root
//@ decreases
func (l *List) InsertAfter(v any, mark *Element /*@, ghost elems set[*Element] @*/) (res *Element) {
	//@ unfold l.Mem(elems, true)
	if mark.list != l {
		//@ fold l.Mem(elems, true)
		return nil
	}
	//@ fold l.Mem(elems, true)
	// see comment in List.Remove about initialization of l
	return l.insertValue(v, mark /*@, elems @*/)
}

// MoveToFront moves element e to the front of list l.
// If e is not an element of l, the list is not modified.
// The element must not be nil.
//@ requires e != nil
//@ requires e != &l.root
//@ requires l.Mem(elems, true) //# Same as 'Remove', we only accept initialized lists and disallow the crash.
//@ requires &l.root in elems   //# This is given by the predicate but explicitly necessary for the postcondition to work without unfolding
//# The next two lines aim to establish: (e.list == l) IFF (e in elems), see top comment in 'Remove' for detailed explanation
//@ requires !(e in elems) ==> (acc(e) && e.list != l)
//@ requires unfolding l.Mem(elems, true) in (e.list == l) == (e in elems)
//@ ensures  l.Mem(elems, true)
//@ ensures  (e in elems && e != old(l.root.nextPure(elems, l))) ==> l.root.comesBefore(e, elems, l)
//@ ensures  (e in elems && e != old(l.root.nextPure(elems, l))) ==> e.comesBefore(old(l.root.nextPure(elems, l)), elems, l)
//@ decreases
func (l *List) MoveToFront(e *Element /*@, ghost elems set[*Element] @*/) {
	//@ unfold l.Mem(elems, true)
	if e.list != l || l.root.next == e {
		//@ fold l.Mem(elems, true)
		return
	}
	//@ fold l.Mem(elems, true)
	// see comment in List.Remove about initialization of l
	l.move(e, &l.root /*@, elems @*/)
}

// MoveToBack moves element e to the back of list l.
// If e is not an element of l, the list is not modified.
// The element must not be nil.
//@ requires e != nil
//@ requires e != &l.root
//@ requires l.Mem(elems, true) //# Same as 'Remove', we only accept initialized lists and disallow the crash.
//@ requires &l.root in elems   //# This is given by the predicate but explicitly necessary for the postcondition to work without unfolding
//# The next two lines aim to establish: (e.list == l) IFF (e in elems), see top comment in 'Remove' for detailed explanation
//@ requires !(e in elems) ==> (acc(e) && e.list != l)
//@ requires unfolding l.Mem(elems, true) in (e.list == l) == (e in elems)
//@ ensures  l.Mem(elems, true)
//@ ensures (e != old(l.root.prevPure(elems, l)) && e != old(l.root.prevPure(elems, l).nextPure(elems, l)) && e in elems) ==> old(l.root.prevPure(elems, l)).comesBefore(e, elems, l)
//@ ensures (e != old(l.root.prevPure(elems, l)) && e != old(l.root.prevPure(elems, l).nextPure(elems, l)) && e in elems) ==> e.comesBefore(old(l.root.prevPure(elems, l).nextPure(elems, l)), elems, l)
//@ decreases
func (l *List) MoveToBack(e *Element /*@, ghost elems set[*Element] @*/) {
	//@ unfold l.Mem(elems, true)
	if e.list != l || l.root.prev == e {
		//@ fold l.Mem(elems, true)
		return
	}
	//@ fold l.Mem(elems, true)
	// see comment in List.Remove about initialization of l
	l.move(e, /*@ unfolding l.Mem(elems, true) in @*/ l.root.prev /*@, elems @*/)
}

// MoveBefore moves element e to its new position before mark.
// If e or mark is not an element of l, or e == mark, the list is not modified.
// The element and mark must not be nil.
//@ requires e != nil
//@ requires e != &l.root
//@ requires mark != nil
//@ requires mark != &l.root
//@ requires l.Mem(elems, true)
//# (e.list == l) IFF (e in elems), see top comment in 'Remove' for detailed explanation
//@ requires !(e in elems) ==> (acc(e) && e.list != l)
//@ requires unfolding l.Mem(elems, true) in (e.list == l) == (e in elems)
//# (mark.list == l) IFF (mark in elems), see top comment in 'Remove' for detailed explanation
//@ requires !(mark in elems) ==> (acc(mark) && mark.list != l)
//@ requires unfolding l.Mem(elems, true) in (mark.list == l) == (mark in elems)
//@ ensures  l.Mem(elems, true)
//@ ensures (e in elems && mark in elems && e != old(mark.prevPure(elems, l)) && e != old(mark.prevPure(elems, l).nextPure(elems, l))) ==> old(mark.prevPure(elems, l)).comesBefore(e, elems, l)
//@ ensures (e in elems && mark in elems && e != old(mark.prevPure(elems, l)) && e != old(mark.prevPure(elems, l).nextPure(elems, l))) ==> e.comesBefore(old(mark.prevPure(elems, l).nextPure(elems, l)), elems, l)
//@ decreases
func (l *List) MoveBefore(e, mark *Element /*@, ghost elems set[*Element] @*/) {
	//@ unfold l.Mem(elems, true)
	if e.list != l || e == mark || mark.list != l {
		//@ fold l.Mem(elems, true)
		return
	}
	//@ fold l.Mem(elems, true)
	l.move(e, /*@ unfolding l.Mem(elems, true) in @*/ mark.prev /*@, elems @*/)
}

// MoveAfter moves element e to its new position after mark.
// If e or mark is not an element of l, or e == mark, the list is not modified.
// The element and mark must not be nil.
//@ requires e != nil
//@ requires e != &l.root
//@ requires mark != nil
//@ requires mark != &l.root
//@ requires l.Mem(elems, true)
//# (e.list == l) IFF (e in elems), see top comment in 'Remove' for detailed explanation
//@ requires !(e in elems) ==> (acc(e) && e.list != l)
//@ requires unfolding l.Mem(elems, true) in (e.list == l) == (e in elems)
//# (mark.list == l) IFF (mark in elems), see top comment in 'Remove' for detailed explanation
//@ requires !(mark in elems) ==> (acc(mark) && mark.list != l)
//@ requires unfolding l.Mem(elems, true) in (mark.list == l) == (mark in elems)
//@ ensures  l.Mem(elems, true)
//@ ensures  (mark != e && e in elems && mark in elems && e != old(mark.nextPure(elems, l))) ==> mark.comesBefore(e, elems, l)
//@ ensures  (mark != e && e in elems && mark in elems && e != old(mark.nextPure(elems, l))) ==> e.comesBefore(old(mark.nextPure(elems, l)), elems, l)
//@ decreases
func (l *List) MoveAfter(e, mark *Element /*@, ghost elems set[*Element] @*/) {
	//@ unfold l.Mem(elems, true)
	if e.list != l || e == mark || mark.list != l {
		//@ fold l.Mem(elems, true)
		return
	}
	//@ fold l.Mem(elems, true)
	l.move(e, mark /*@, elems @*/)
}

//# Both 'PushBackList' and 'PushFrontList' could not yet be successfully verified.
//# Neither code, nor comment make explicitly clear that they expect 'other' to already be initialized.
//# This is not a problem if l==other since both methods call l.lazyInit(..) to make sure l is initialized.
//# Therefore it makes sense to have 'requires (l != other) ==> (other.Mem(elemsOther, true))' as a precondition and enfore 'other' to be initialized.
//# For the loop invariant there is a difficulty in establishing the relationship between the decreasing i
//# and the advances along the list in the calls to 'e.Next(..)' and 'e.Prev(..)' respectively.
//# If l!=other then we want that i==0 at the same time as 'e.Next/Prev(..)' returns nil.
//# If l==other then this is not the case since the head/tail of the list gets continually updated.
//# We need to establish that the 'Len()' many calls to 'e.Next/Prev(..)' returned us every element of the original list exactly once.
//# Another issue is that the elements get cloned (i.e. we call 'insertValue' in the loop) which has the challenge
//# of establishing a postcondition that l's elements now contain all the original elements from 'elemsL' and clones from 'elemsOther'. 

// PushBackList inserts a copy of another list at the back of list l.
// The lists l and other may be the same. They must not be nil.
//@ requires false
func (l *List) PushBackList(other *List /*@, ghost elemsL set[*Element], ghost elemsOther set[*Element], ghost isInit bool @*/) {
	l.lazyInit(/*@ elemsL, isInit @*/)
	for i, e := other.Len(/*@ elemsOther, true @*/), other.Front(/*@ elemsOther @*/); i > 0; i, e = i-1, e.Next(/*@ elemsOther, other @*/) {
		l.insertValue(e.Value, l.root.prev /*@, elemsL @*/)
	}
}

// PushFrontList inserts a copy of another list at the front of list l.
// The lists l and other may be the same. They must not be nil.
//@ requires false
//@ requires l.Mem(elemsL,isInit)
//@ requires (l == other) ==> (elemsL == elemsOther)
//@ requires (l != other) ==> (other.Mem(elemsOther, true))
func (l *List) PushFrontList(other *List /*@, ghost elemsL set[*Element], ghost elemsOther set[*Element], ghost isInit bool @*/) {
	l.lazyInit(/*@elemsL, isInit @*/)
	//@ assert l.Mem(elemsL, true)
	for i, e := other.Len(/*@ elemsOther, true @*/), other.Back(/*@ elemsOther @*/); i > 0; i, e = i-1, e.Prev(/*@ elemsOther, other @*/) {
		//@ unfold other.Mem(elemsOther, true) //# different if l==other
		eValue := e.Value
		//@ fold other.Mem(elemsOther, true) //# different if l==other
		newElem := l.insertValue(eValue, &l.root /*@, elemsL @*/)
	}
}
