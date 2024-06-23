import Mathlib
import Mathlib.Data.Opposite

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite

variable {A B C : Type} [Category A] [Category B]

structure RatCat (F : A × Bᵒᵖ ⥤ A) where
  over : A
  under : B

abbrev CategoryTheory.Functor.obj₂ (F : A × B ⥤ A) : A → B → A :=
  λ α β => (F.obj α).obj β

#check NatTrans

def CategoryTheory.Functor.map₂ (F : A ⥤ B ⥤ A) {Xl Xr : A} {Yl Yr : B}
  (f : Xl ⟶ Xr)
  (g : Yl ⟶ Yr)
  : F.obj₂ Xl Yl ⟶ F.obj₂ Xr Yr := by
   simp [CategoryTheory.Functor.obj₂]
   have := (F.map f) ≫ g


def RatCat.mkHom {P : A ⥤ Bᵒᵖ ⥤ A} (σ τ : RatCat P) : Type :=
  P.obj₂ σ.over (op τ.under) ⟶ P.obj₂ τ.over (op σ.under)

def RatCatAux (P : A ⥤ Bᵒᵖ ⥤ A) := ∀ {Xl Xr Y Zl Zr},
  (P.obj₂ (P.obj₂ Xl Y) Zl ⟶ P.obj₂ (P.obj₂ Xr Y) Zr) → (P.obj₂ (P.obj₂ Xl Y) Zl ⟶ P.obj₂ (P.obj₂ Xr Y) Zr)

instance {P : A ⥤ Bᵒᵖ ⥤ A} (aux : RatCatAux P) : CategoryStruct (RatCat P) where
  Hom := λ σ τ => RatCat.mkHom σ τ
  id σ := 𝟙 (P.obj₂ σ.over (op σ.under))
  comp {X Y Z} f g := by
    simp [RatCat.mkHom]
    simp [RatCat.mkHom] at g
    simp [RatCat.mkHom] at f
    have id_d := 𝟙 <| op (Y.under)
    have := P.map₂ f id_d
