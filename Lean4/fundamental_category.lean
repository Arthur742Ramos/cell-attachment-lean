module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Lean4.directed_path_homotopy
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

@[expose] public section


/-
  This file contains the definition of the fundamental category of a directed space.
  We follow the structure of the undirected version found at:
  https://leanprover-community.github.io/mathlib_docs/algebraic_topology/fundamental_groupoid/basic.html#fundamental_groupoid
-/

open DirectedMap
open CategoryTheory

universe u v
variable {X : Type u} {Y : Type v} [DirectedSpace X] [DirectedSpace Y] {x₀ x₁ : X}

open scoped unitInterval

noncomputable section

namespace Dipath

namespace Dihomotopy

open Path.Homotopy

section assoc

lemma transAssocReparamAux_directed : DirectedMap.Directed
  ({ toFun := fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩} : C(I, I)) := by
  apply DirectedUnitInterval.directed_of_monotone _
  intros x y hxy
  unfold transAssocReparamAux
  simp
  have : (x : ℝ) ≤ (y : ℝ) := hxy
  split_ifs with h₀ h₁ h₂ h₃ h₄ h₅
  · linarith
  · linarith
  · push_neg at h₂
    have : 0 ≤ (y : ℝ) := le_trans (by norm_num) (le_of_lt h₂)
    have : 1 ≤ (y : ℝ) + 1 := by linarith
    calc 2 * (x : ℝ)
      _ ≤ 2 * 4⁻¹ := (mul_le_mul_iff_of_pos_left (by norm_num)).mpr h₀
      _ = (2⁻¹ : ℝ) * 1 := by norm_num
      _ ≤ (2⁻¹ : ℝ) * (↑y + 1) := (mul_le_mul_iff_of_pos_left (by norm_num)).mpr this
  · linarith
  · linarith
  · push_neg at h₅
    calc (x : ℝ) + (4⁻¹ : ℝ)
      _ = 4⁻¹ + ↑x := by ring
      _ ≤ 4⁻¹ + 2⁻¹ := add_le_add_right h₃ 4⁻¹
      _ = 2⁻¹ + 4⁻¹ := by ring
      _ = 2⁻¹ * (2⁻¹ + 1) := by norm_num
      _ ≤ 2⁻¹ * (↑y + 1) := (mul_le_mul_iff_of_pos_left (by norm_num)).mpr (by linarith)
  · linarith
  · linarith
  · apply (mul_le_mul_iff_of_pos_left (show 0 < (2⁻¹ : ℝ) by norm_num)).mpr
    linarith [Subtype.coe_le_coe.mpr hxy]

def transAssocReparamAuxMap : D(I, I) where
  toFun := fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩
  directed_toFun := transAssocReparamAux_directed

lemma trans_assoc_reparam_directed {x₀ x₁ x₂ x₃ : X} (p : Dipath x₀ x₁) (q : Dipath x₁ x₂) (r : Dipath x₂ x₃) :
    (p.trans q).trans r = (p.trans (q.trans r)).reparam
      transAssocReparamAuxMap
      (Subtype.ext transAssocReparamAux_zero)
      (Subtype.ext transAssocReparamAux_one) := by
  ext t
  have : (p.trans q).trans r t =  (p.toPath.trans q.toPath).trans r.toPath t := rfl
  rw [this, trans_assoc_reparam p.toPath q.toPath r.toPath]
  rfl

/--
For any three dipaths `p q r`, `(p.trans q).trans r` is dihomotopic with `p.trans (q.trans r)`.
-/
def trans_assoc {x₀ x₁ x₂ x₃ : X} (p : Dipath x₀ x₁) (q : Dipath x₁ x₂) (r : Dipath x₂ x₃) :
    ((p.trans q).trans r).Dihomotopic (p.trans (q.trans r)) := by
  have := Dihomotopic.reparam (p.trans (q.trans r)) transAssocReparamAuxMap
    (Subtype.ext transAssocReparamAux_zero)
    (Subtype.ext transAssocReparamAux_one)
  rw [←trans_assoc_reparam_directed] at this
  exact Relation.EqvGen.symm _ _ this

end assoc

end Dihomotopy

end Dipath

/-
 Definition of the fundamental category and of the functor sending a directed space to its
 fundamental category
-/
@[ext]
structure FundamentalCategory (X : Type u) where
  as : X

namespace FundamentalCategory

@[simps]
def equiv (X : Type*) : FundamentalCategory X ≃ X where
  toFun x := x.as
  invFun x := .mk x
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma isEmpty_iff (X : Type*) :
    IsEmpty (FundamentalCategory X) ↔ IsEmpty X :=
  equiv _ |>.isEmpty_congr

instance (X : Type*) [IsEmpty X] :
    IsEmpty (FundamentalCategory X) :=
  equiv _ |>.isEmpty

@[simp]
lemma nonempty_iff (X : Type*) :
    Nonempty (FundamentalCategory X) ↔ Nonempty X :=
  equiv _ |>.nonempty_congr

instance (X : Type*) [Nonempty X] :
    Nonempty (FundamentalCategory X) :=
  equiv _ |>.nonempty

@[simp]
lemma subsingleton_iff (X : Type*) :
    Subsingleton (FundamentalCategory X) ↔ Subsingleton X :=
  equiv _ |>.subsingleton_congr

instance (X : Type*) [Subsingleton X] :
    Subsingleton (FundamentalCategory X) :=
  equiv _ |>.subsingleton


instance {X : Type u} [Inhabited X] : Inhabited (FundamentalCategory X) :=
  ⟨⟨default⟩⟩

attribute [local instance] Dipath.Dihomotopic.setoid

instance : CategoryTheory.Category (FundamentalCategory X) where
  Hom x y := Dipath.Dihomotopic.Quotient x.as y.as
  id x := ⟦Dipath.refl x.as⟧
  comp {_ _ _} := Dipath.Dihomotopic.Quotient.comp
  id_comp {x _} f :=
    Quotient.inductionOn f fun a =>
      show ⟦(Dipath.refl x.as).trans a⟧ = ⟦a⟧ from Quotient.sound (Relation.EqvGen.rel _ _ ⟨Dipath.Dihomotopy.refl_trans a⟩)
  comp_id {_ y} f :=
    Quotient.inductionOn f fun a =>
      show ⟦a.trans (Dipath.refl y.as)⟧ = ⟦a⟧ from Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨Dipath.Dihomotopy.trans_refl a⟩))
  assoc {_ _ _ _} f g h :=
    Quotient.inductionOn₃ f g h fun p q r =>
      show ⟦(p.trans q).trans r⟧ = ⟦p.trans (q.trans r)⟧ from
        Quotient.sound (Dipath.Dihomotopy.trans_assoc p q r)

lemma comp_eq (x y z : FundamentalCategory X) (p : x ⟶ y) (q : y ⟶ z) :
    p ≫ q = p.comp q := rfl

lemma id_eq_path_refl (x : FundamentalCategory X) :
    𝟙 x = ⟦Dipath.refl x.as⟧ := rfl

@[reducible]
def fundamentalCategoryFunctor : dTopCat ⥤ CategoryTheory.Cat where
      obj X := { α := FundamentalCategory X }
      map f := { toFunctor := {
      obj := fun x => ⟨f x.as⟩
      map := fun {X Y} p => by exact p.mapFn f
      map_id := fun X => by
        change Dipath.Dihomotopic.Quotient.mapFn
          ⟦Dipath.refl X.as⟧ f = ⟦Dipath.refl (f X.as)⟧
        rw [← Dipath.Dihomotopic.map_lift]
        congr 1
      map_comp := fun {x y z} p q => by
        refine Quotient.inductionOn₂ p q fun a b => ?_
        change Dipath.Dihomotopic.Quotient.mapFn
          (Dipath.Dihomotopic.Quotient.comp ⟦a⟧ ⟦b⟧) f =
          Dipath.Dihomotopic.Quotient.comp ⟦a.map f⟧ ⟦b.map f⟧
        rw [←Dipath.Dihomotopic.comp_lift a b,
          ←Dipath.Dihomotopic.map_lift (a.trans b) f,
          Dipath.map_trans,
          ←Dipath.Dihomotopic.comp_lift]
    }}

      map_id X := by
        apply CategoryTheory.Cat.ext
        simp only
        change _ = 𝟭 (FundamentalCategory X)
        congr
        ext x y p
        refine' Quotient.inductionOn p fun q => _
        rw [← Dipath.Dihomotopic.map_lift]
        conv_rhs => rw [←q.map_id]
        rfl

      map_comp f g := by
        apply CategoryTheory.Cat.ext
        simp only
        congr
        ext x y p
        refine' Quotient.inductionOn p fun q => _
        simp only [Quotient.map_mk, Dipath.map_map, Quotient.eq']
        rfl

scoped notation "dπ" => FundamentalCategory.fundamentalCategoryFunctor
scoped notation "dπₓ" => FundamentalCategory.fundamentalCategoryFunctor.obj
scoped notation "dπₘ" => FundamentalCategory.fundamentalCategoryFunctor.map

lemma map_eq {X Y : dTopCat} {x₀ x₁ : X} (f : D(X, Y)) (p : Dipath.Dihomotopic.Quotient x₀ x₁) :
  (dπₘ f).toFunctor.map p = p.mapFn f := rfl

/-- Help the typechecker by converting a point in the fundamental category back to a point in
the underlying directed space. -/
@[reducible]
def toTop {X : dTopCat} (x : dπₓ X) : X := x.as

/-- Help the typechecker by converting a point in a directed space to a
point in the fundamental category of that space -/
@[reducible]
def fromTop {X : dTopCat} (x : X) : dπₓ X := ⟨x⟩

/-- Help the typechecker by converting an arrow in the fundamental category of
a directed space back to a directed path in that space (i.e., `Dipath.Dihomotopic.Quotient`). -/
@[reducible]
def toPath {X : dTopCat} {x₀ x₁ : dπₓ X} (p : x₀ ⟶ x₁) :
  Dipath.Dihomotopic.Quotient (X := X) x₀.as x₁.as := p

/-- Help the typechecker by convering a directed path in a directed space to an arrow in the
fundamental category of that space. -/
@[reducible]
def fromPath {X : dTopCat} {x₀ x₁ : X} (p : Dipath.Dihomotopic.Quotient x₀ x₁) :
  FundamentalCategory.mk x₀ ⟶ FundamentalCategory.mk x₁ := p

end FundamentalCategory

