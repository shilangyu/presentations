import Aesop

structure NonEmptyList (α : Type) where
  data : List α
  nonEmpty : !data.isEmpty

def new (head : α) (rest : List α) : NonEmptyList α :=
  NonEmptyList.mk (head :: rest) (by simp_all only [List.isEmpty_cons, Bool.not_false])

def head (l : NonEmptyList α) : α :=
  l.data.head (by
    have h := l.nonEmpty
    simp_all only [Bool.not_eq_true', ne_eq]
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp_all only [List.isEmpty_nil, Bool.true_eq_false]
  )

def prepend (l : NonEmptyList α) (e : α) : NonEmptyList α :=
  NonEmptyList.mk (e :: l.data) (by
    simp_all only [List.isEmpty_cons, Bool.not_false]
  )
