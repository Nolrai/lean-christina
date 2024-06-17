import Mathlib
import Mathlib.Data.Set.Finite

open Filter

structure Lifted (α : Type u) where
  val : Filter α

postfix:50 "⋆ " => Lifted

-- this is constructively a stronger statment then Filter.NeBot
abbrev Lifted.toProp (L : α⋆) : Prop := ∀ s ∈ L.val, ∃ x, x ∈ s

@[simp]
theorem Lifted.toProp_toNeBot (F : Filter α) : Lifted.toProp ⟨F⟩ → F.NeBot := by
  simp [Lifted.toProp, Filter.neBot_iff]
  intros lifted_toProp filter_eq_bot
  cases filter_eq_bot
  have ⟨_, ff⟩ := lifted_toProp ∅ (Filter.mem_bot)
  apply ff

prefix:40 "¿" => Lifted.toProp

instance : Pure (·⋆) where
  pure a := ⟨pure a⟩

instance : Monad (·⋆) where
  bind := λ x y => ⟨Filter.bind x.val (Lifted.val ∘ y)⟩

theorem constMap_neBot {α β} (L : α⋆) (b : β) : L $> b = pure b ↔ ¿L := by
  simp [Functor.mapConstRev, Functor.mapConst, Pure.pure, Filter.ext_iff]
  have ⟨⟨L_sets, L_univ_sets, _, _⟩⟩ := L
  simp [Filter.neBot_iff, ← empty_mem_iff_bot]
  constructor
  case mp =>
    intros h h'
    have := h ∅
    simp_all
  case mpr =>
    intros L_nonbot s
    by_cases b ∈ s
    case pos b_in_s =>
      simp_all
      exact ⟨Set.univ, L_univ_sets⟩
    case neg b_nin_s =>
      simp_all

instance : LawfulFunctor (·⋆) where
  map_const := rfl
  id_map _x := rfl
  comp_map _g _h _x := rfl

instance : LawfulApplicative (·⋆) where
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  map_pure _ _ := rfl
  seq_pure _ _ := rfl
  seq_assoc _ _ _ := rfl

instance : LawfulMonad (·⋆) where
  bind_pure_comp _f _x := rfl
  bind_map _f _x := rfl
  pure_bind _x _f := rfl
  bind_assoc _x _f _g := rfl

def Omega [Preorder α] : α⋆ := ⟨Filter.atTop⟩

-- apply a predicate to a filter, that is "filter" here is like List.lifter, not the Filter Type.
def Lifted.filter (P : α → Prop) (a : α⋆) : α⋆ :=
  ⟨𝓟 (P : Set α) ⊓ a.val⟩

instance : Coe (Set α) (α⋆) where
  coe := λ s => ⟨𝓟 (· ∈ s)⟩

theorem Lifted.ext : (x y : α⋆) → x.val.sets = y.val.sets → x = y := by
  intros x y h
  have ⟨⟨_, _, _, _⟩⟩ := x
  have ⟨⟨_, _, _, _⟩⟩ := y
  aesop

theorem Lifted.aux₁ {α} (S : Set α) : ({val := 𝓟 S} : Lifted α).val.sets = { s | S ⊆ s} := by
  simp_all only
  apply Eq.refl

@[simp]
theorem Lifted.seq_sets (x : α⋆) (y : β⋆) : (f <$> x <*> y).val.sets = {s | {a | {b | f a b ∈ s} ∈ y.val} ∈ x.val} := by
  simp [Seq.seq, Functor.map, pure, Filter.bind, map, join]

theorem Lifted.lifts_applicative (f : α → β → γ) (s : Set α) (t : Set β) :
  ↑(f <$> s <*> t : Set γ) = f <$> (↑s : α⋆) <*> ↑t := by
  apply Lifted.ext
  rw [Lifted.aux₁]
  simp
  ext i
  apply Iff.intro
  case a.h.mp =>
    intro h
