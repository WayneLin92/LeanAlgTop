import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators


set_option autoImplicit false

open CategoryTheory MonoidalCategory Limits
open scoped MonoidalCategory BigOperators

universe v u x


noncomputable section temporary_fixes

namespace CategoryTheory.Limits

universe w w₁

variable {β : Type w}

variable {C : Type u} [Category.{v} C]

variable {γ : Type w₁} (ε : β ≃ γ) (f : γ → C)

section

variable [HasProduct f] [HasProduct (f ∘ ε)]

/-- Reindex a categorical product via an equivalence of the index types. -/
def Pi'.reindex : piObj (f ∘ ε) ≅ piObj f :=
  HasLimit.isoOfEquivalence (Discrete.equivalence ε) (Discrete.natIso fun _ => Iso.refl _)

@[reassoc (attr := simp)]
theorem Pi'.reindex_hom_π (b : β) : (Pi'.reindex ε f).hom ≫ Pi.π f (ε b) = Pi.π (f ∘ ε) b := by
  dsimp [Pi'.reindex]
  simp only [HasLimit.isoOfEquivalence_hom_π, Discrete.equivalence_inverse, Discrete.functor_obj,
    Function.comp_apply, Functor.id_obj, Discrete.equivalence_functor, Functor.comp_obj,
    Discrete.natIso_inv_app, Iso.refl_inv, Category.id_comp]
  exact limit.w (Discrete.functor (f ∘ ε)) (Discrete.eqToHom' (ε.symm_apply_apply b))

@[reassoc (attr := simp)]
theorem Pi'.reindex_inv_π (b : β) : (Pi'.reindex ε f).inv ≫ Pi.π (f ∘ ε) b = Pi.π f (ε b) := by
  simp [Iso.inv_comp_eq]

end

end CategoryTheory.Limits

end temporary_fixes


def PermCat := ℕ

namespace PermCat

instance (n : ℕ) : OfNat PermCat n := ⟨n⟩

instance : Groupoid PermCat where
  Hom (n m : ℕ) := Fin n ≃ Fin m
  id (n : ℕ) := .refl _
  comp := .trans
  inv := .symm

end PermCat

variable (V : Type u) [Category.{v} V] [HasFiniteProducts V]



structure Operad extends PermCat ⥤ V where
  unit : ⊤_ V ⟶ obj 1
  comp {k : ℕ} (n : Fin k → ℕ) :
    (obj k ⨯ ∏ (obj ∘ n)) ⟶ obj (∑ i, n i : ℕ)
  unit_comp (n : ℕ) : (prod.leftUnitor (obj n)).inv ≫
    (prod.map unit (productUniqueIso (obj ∘ ![n])).inv) ≫ comp ![n] = 𝟙 (obj n)
  comp_unit (n : ℕ) :
    (prod.rightUnitor (obj n)).inv ≫ (prod.map (𝟙 _) (Pi.lift (fun _ ↦ unit))) ≫
      comp (fun _ : Fin n ↦ 1) ≫ eqToHom (by simp) = 𝟙 (obj n)
  equivariance {k : ℕ} (e : Fin k ≃ Fin k) (n : Fin k → ℕ) :
    (prod.map (map e) (𝟙 _)) ≫ comp n =
      (prod.map (𝟙 _) (Pi'.reindex e (obj ∘ n)).inv) ≫ comp (n ∘ e) ≫ eqToHom
      (congr_arg obj (Equiv.sum_comp e n))
  assoc {k : ℕ} (j : Fin k → ℕ) (i : (s : Fin k) → (Fin (j s)) → ℕ) : sorry



def f3 : Fin 4 :=
  Fin.ofNat 3

theorem sub_lt {a b c : Nat} (h1 : a < b) (h2 : c <= a) : (a - c < b - c) :=
  have h3: a - c + c < b - c + c


def f {a b : ℕ} (x : Fin (a + b)) : (Fin a) ⊕ (Fin b) := 
  if h : x.val < a then Sum.inl ⟨x.val, h⟩
  else Sum.inr ⟨x.val - a, sorry⟩

#check Nat.add_sub_cancel_left