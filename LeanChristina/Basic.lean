import Mathlib
import Mathlib.Data.Opposite

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite

variable {A B C : Type} [Category A] [Category B] [Category C]

structure RatCat (profunctor : A ⥤ Bᵒᵖ ⥤ C) where
  over : A
  under : B

def CategoryTheory.Functor.obj2 (profunctor : A ⥤ B ⥤ C) : A → B → C :=
  λ α β => (profunctor.obj α).obj β

def RatCat.mkHom {P : A ⥤ Bᵒᵖ ⥤ C} (σ τ : RatCat P) : Type :=
  P.obj2 σ.over (op τ.under) ⟶ P.obj2 τ.over (op σ.under)

instance {P : A ⥤ Bᵒᵖ ⥤ C} : Category (RatCat P) where
  Hom := λ σ τ => RatCat.mkHom σ τ
  id σ := 𝟙 (P.obj2 σ.over (op σ.under))
  comp := by simp
