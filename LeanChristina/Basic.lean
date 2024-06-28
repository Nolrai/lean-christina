import Mathlib

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite CategoryTheory.Monoidal

section

variable {A B C : Type} [Category A] [Category B]

abbrev CategoryTheory.Functor.obj₂ (F : A × B ⥤ A) : A → B → A :=
  λ α β => (F.obj ⟨α, β⟩)

def CategoryTheory.Functor.map₂ (F : A × B ⥤ A) {Xl Xr : A} {Yl Yr : B}
  (f : Xl ⟶ Xr)
  (g : Yl ⟶ Yr)
  : F.obj₂ Xl Yl ⟶ F.obj₂ Xr Yr := F.map ⟨f, g⟩

end

class PairAction (A : outParam Type) (B) extends Category B where
  mul : Bᵒᵖ × Bᵒᵖ ⥤ Bᵒᵖ
  toCategoryA : Category A
  smul : A × Bᵒᵖ ⥤ A
  iso : ∀ (a : A) (b₁ b₂ : Bᵒᵖ), smul.obj₂ (smul.obj₂ a b₁) b₂ ≅ smul.obj₂ a (mul.obj₂ b₁ b₂)

infix:50 " •. " => PairAction.smul.obj₂
infix:50 " •' " => PairAction.smul.map₂

structure RatCat {A} (B : Type) [PairAction A B] where
  over : A
  under : B

def RatCat.mkHom [PairAction A B] (σ τ : RatCat B)  : Type :=
  σ.over •. (op τ.under) ⟶ τ.over •. (op σ.under)

def RatCatAux [PairAction A B] := ∀ {Xl Xr Y Zl Zr},
  (P.obj₂ (P.obj₂ Xl Y) Zl ⟶ P.obj₂ (P.obj₂ Xr Y) Zr) → (P.obj₂ (P.obj₂ Xl Y) Zl ⟶ P.obj₂ (P.obj₂ Xr Y) Zr)

instance [PairAction] (aux : RatCatAux P) : CategoryStruct (RatCat P) where
  Hom := λ σ τ => RatCat.mkHom σ τ
  id σ := 𝟙 (P.obj₂ σ.over (op σ.under))
  comp {X Y Z} f g := by
    simp [RatCat.mkHom]
    simp [RatCat.mkHom] at g
    simp [RatCat.mkHom] at f
    have id_d := 𝟙 <| op (Y.under)
    have := P.map₂ f id_d
    cases P
    case mk inst₁ inst₂ P map_id map_comp =>
    have ⟨obj, map⟩ := P
    simp [Functor.obj₂, Functor.map₂] at *
    have ⟨Xu, Xd⟩ := X
    have ⟨Yu, Yd⟩ := Y
    have ⟨Zu, Zd⟩ := Z
    simp [Functor.obj₂, Functor.map₂] at *
    simp [Functor.obj₂, Functor.map₂] at g
    simp [Functor.obj₂, Functor.map₂] at f
    simp [Functor.obj₂, Functor.map₂] at this
