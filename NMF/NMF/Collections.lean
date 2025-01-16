import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import NMF.MutableTypeCategories

open CategoryTheory

universe u

variable (Ω : Type u)

namespace MutableTypeCategories

/-
# Lazy Collections
-/

open Finset
open Multiset
open Set
open List

structure LazyCollection (T : Type u → Type u) (A : Type u) where
  eval : Ω → T A

abbrev LazyPowerset (A : Type u) := LazyCollection Ω Finset A

abbrev LazyMultiset (A : Type u) := LazyCollection Ω Multiset A

abbrev LazyList (A : Type u) := LazyCollection Ω List A

abbrev LazySet (A : Type u) := LazyCollection Ω Set A

@[simp]
def lazy_set_func {A B : Type u} (f : morph Ω A B) : morph Ω (LazySet Ω A) (LazySet Ω B) :=
  fun (s : (LazySet Ω A) × Ω) => ({
    eval:= fun (ω : Ω) => { b : B | ∃ a, a ∈ (s.1.eval ω) ∧ b = (f (a, ω)).1 }
  }, s.2)

@[simp]
def lazy_powerset_func {A B : Type u} (f : morph Ω A B) [DecidableEq B] : morph Ω (LazyPowerset Ω A) (LazyPowerset Ω B) :=
  fun (s : (LazyPowerset Ω A) × Ω) => ({
    eval:= fun (ω : Ω) =>
    let m := (s.1.eval ω).val.map (fun (a : A) => (f (a,ω)).1)
    {
      val := m.dedup
      nodup := Multiset.dedup_eq_self.mp m.dedup_idem
    }
  }, s.2)

@[simp]
def lazy_multiset_func {A B : Type u} (f : morph Ω A B) : morph Ω (LazyMultiset Ω A) (LazyMultiset Ω B) :=
  fun (s : (LazyMultiset Ω A) × Ω) => ({
    eval:= fun (ω : Ω) => (s.1.eval ω).map (fun (a : A) => (f (a,ω)).1)
  }, s.2)

@[simp]
def lazy_list_func {A B : Type u} (f : morph Ω A B) : morph Ω (LazyList Ω A) (LazyList Ω B) :=
  fun (s : (LazyList Ω A) × Ω) => ({
    eval:= fun (ω : Ω) => (s.1.eval ω).map (fun (a : A) => (f (a,ω)).1)
  }, s.2)

@[simp]
def lift_set_lazy {A Ω : Type u} (set : Set A) : LazySet Ω A
  := {
    eval := fun (_ : Ω) => set
  }

@[simp]
def lift_list_lazy {A Ω : Type u} (list : List A) : LazyList Ω A
  := {
    eval := fun (_ : Ω) => list
  }

lemma lazy_set_func_sideeffect_free {A B : Type u} (f : morph Ω A B) :
  side_effect_free (lazy_set_func Ω f)
  := by simp

lemma lazy_powerset_func_sideeffect_free {A B : Type u} [DecidableEq B] (f : morph Ω A B) :
  side_effect_free (lazy_powerset_func Ω f)
  := by simp

lemma lazy_multiset_func_sideeffect_free {A B : Type u} (f : morph Ω A B) :
  side_effect_free (lazy_multiset_func Ω f)
  := by simp

lemma lazy_list_func_sideeffect_free {A B : Type u} (f : morph Ω A B) :
  side_effect_free (lazy_list_func Ω f)
  := by simp

@[simp]
def unit_lazy_set { A B : Type u} (f : morph Ω A B) : morph Ω A (LazySet Ω B)
  := fun (a,ω2) => ({
    eval := fun ω => { (f (a,ω)).1 }
  }, ω2)

@[simp]
def unit_lazy_multiset { A B : Type u} (f : morph Ω A B) : morph Ω A (LazyMultiset Ω B)
  := fun (a,ω2) => ({
    eval := fun ω => { (f (a,ω)).1 }
  }, ω2)

@[simp]
def unit_lazy_powerset { A B : Type u} (f : morph Ω A B) : morph Ω A (LazyPowerset Ω B)
  := fun (a,ω2) => ({
    eval := fun ω => { (f (a,ω)).1 }
  }, ω2)

@[simp]
def unit_lazy_list { A B : Type u} (f : morph Ω A B) : morph Ω A (LazyList Ω B)
  := fun (a,ω2) => ({
    eval := fun ω => [ (f (a,ω)).1 ]
  }, ω2)

structure OrderedSet (A : Type u) where
  items : List A
  nodup : Nodup items

structure LazyOrderedSet (A : Type u) where
  eval : Ω → OrderedSet A

end MutableTypeCategories
