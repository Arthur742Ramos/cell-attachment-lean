module

/-
Copyright (c) 2026 Ruize Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruize Chen

This is a local backport from mathlib commit
389347a7c1cfa76f6bd5be2ca35d4cb621610ad3, file
Mathlib/Topology/Covering/FundamentalGroupCircle.lean (Apache 2.0):
https://github.com/leanprover-community/mathlib4/blob/389347a7c1cfa76f6bd5be2ca35d4cb621610ad3/Mathlib/Topology/Covering/FundamentalGroupCircle.lean
The supporting lifting lemmas below are backported from the same commit's
Mathlib/Topology/Homotopy/Lifting.lean, copyright (c) 2025 Junyan Xu.
https://github.com/leanprover-community/mathlib4/blob/389347a7c1cfa76f6bd5be2ca35d4cb621610ad3/Mathlib/Topology/Homotopy/Lifting.lean
The zmultiples equivalence is adapted, specialized to real numbers, from
Mathlib/Algebra/Group/Subgroup/ZPowers/Lemmas.lean, copyright (c) 2020
Chris Hughes, authors Chris Hughes and Snir Broshi (Apache 2.0).
https://github.com/leanprover-community/mathlib4/blob/389347a7c1cfa76f6bd5be2ca35d4cb621610ad3/Mathlib/Algebra/Group/Subgroup/ZPowers/Lemmas.lean
All additions after `end AddCircle` are project-specific.
-/

public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.ZMultiples
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section


/-!
# The fundamental group of the circle

For `0 < p`, the fundamental group of `AddCircle p` at any basepoint is isomorphic to `ℤ`
(`AddCircle.windingNumberIso`). The winding number `AddCircle.windingNumber` of a loop is
`(f 1 - f 0) / p` for any continuous lift `f : I → ℝ` of the loop
(`AddCircle.windingNumber_eq_div`); in particular the loop `t ↦ n • (t * p) + x` has winding
number `n` (`AddCircle.windingNumber_zsmulLoop`).
-/


open unitInterval

noncomputable section

namespace AddSubgroup

/-- Backported real specialization of the integer-multiples equivalence. -/
def zmultiplesEquivInt {a : ℝ} (ha : a ≠ 0) : zmultiples a ≃+ ℤ :=
  ((AddMonoidHom.ofInjective (show Function.Injective (zmultiplesHom ℝ a) from
    smul_left_injective ℤ ha)).trans
    (AddEquiv.addSubgroupCongr (range_zmultiplesHom a))).symm

@[simp]
theorem coe_zmultiplesEquivInt_symm_apply {a : ℝ} (ha : a ≠ 0) (n : ℤ) :
    ((zmultiplesEquivInt ha).symm n : ℝ) = n • a := by
  simp only [zmultiplesEquivInt, AddEquiv.symm_symm, AddEquiv.trans_apply,
    AddEquiv.addSubgroupCongr_apply, AddMonoidHom.ofInjective_apply, zmultiplesHom_apply]

@[simp]
theorem zmultiplesEquivInt_apply_zsmul {a : ℝ} (ha : a ≠ 0) (n : ℤ) :
    zmultiplesEquivInt ha ⟨n • a, zsmul_mem_zmultiples a n⟩ = n :=
  (zmultiplesEquivInt ha).eq_symm_apply.mp (Subtype.ext (by simp))

end AddSubgroup

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
  (cov : IsCoveringMap p)

theorem coe_monodromy_mk {x y : X} (γ : Path x y) (e : p ⁻¹' {x}) :
    (cov.monodromy (.mk γ) e : E) = cov.liftPath γ e (γ.source.trans e.2.symm) 1 :=
  rfl

lemma monodromy_eq_apply_one {x y : X} {γ : Path x y} {e : p ⁻¹' {x}} {Γ : C(I, E)}
    (hpΓ : p ∘ Γ = γ) (Γ_0 : Γ 0 = e) : cov.monodromy (.mk γ) e = Γ 1 := by
  rw [show Γ = cov.liftPath γ e (γ.source.trans e.2.symm) from
    (eq_liftPath_iff' ..).mpr ⟨hpΓ, Γ_0⟩, coe_monodromy_mk]

end IsCoveringMap

namespace IsQuotientCoveringMap

variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [Group G] [MulAction G E] {p : E → X} (hp : IsQuotientCoveringMap p G)
  {x : X} (e : p ⁻¹' {x}) {γ : FundamentalGroup X x} {g : G}

theorem fundamentalGroupToMulOpposite_apply_mk_eq {e : p ⁻¹' {x}}
    {γ : Path x x} {g : G} {Γ : C(I, E)}
    (hpΓ : p ∘ Γ = γ) (Γ_0 : Γ 0 = e) (Γ_1 : Γ 1 = g • e) :
    hp.fundamentalGroupToMulOpposite e (.mk γ) = .op g :=
  hp.fundamentalGroupToMulOpposite_apply_eq_Iff.mpr <| by
    simp [hp.isCoveringMap.monodromy_eq_apply_one hpΓ Γ_0, Γ_1]

theorem fundamentalGroupToMulOpposite_toPermFiber :
    hp.fundamentalGroupToMulOpposite (hp.toPermFiber x g e) γ =
      MulOpposite.op (g * (hp.fundamentalGroupToMulOpposite e γ).unop * g⁻¹) := by
  rw [fundamentalGroupToMulOpposite_apply_eq_Iff, hp.monodromy_toPermFiber]
  simp only [MulOpposite.unop_op, toPermFiber_apply_apply_coe,
    ← hp.unop_fundamentalGroupToMulOpposite_smul, mul_smul, inv_smul_smul]

theorem fundamentalGroupToMulOpposite_eq [IsMulCommutative G] (e' : p ⁻¹' {x}) :
    hp.fundamentalGroupToMulOpposite e = hp.fundamentalGroupToMulOpposite e' := by
  obtain ⟨g, rfl⟩ := hp.exists_toPermFiber_eq e e'
  ext γ
  rw [fundamentalGroupToMulOpposite_toPermFiber, mul_comm' g, mul_inv_cancel_right,
    MulOpposite.op_unop]

theorem fundamentalGroupEquiv_eq [SimplyConnectedSpace E] [IsMulCommutative G]
    (e' : p ⁻¹' {x}) : hp.fundamentalGroupEquiv e = hp.fundamentalGroupEquiv e' :=
  MulEquiv.ext fun γ ↦ congr($(hp.fundamentalGroupToMulOpposite_eq e e') γ)

end IsQuotientCoveringMap

namespace IsAddQuotientCoveringMap

variable {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [AddGroup G] [AddAction G E] {p : E → X} (hp : IsAddQuotientCoveringMap p G)
  {x : X} (e : p ⁻¹' {x})

theorem fundamentalGroupToMulOpposite_apply_mk_eq {e : p ⁻¹' {x}}
    {γ : Path x x} {g : Multiplicative G}
    {Γ : C(I, E)} (hpΓ : p ∘ Γ = γ) (Γ_0 : Γ 0 = e) (Γ_1 : Γ 1 = g • e) :
    hp.fundamentalGroupToMulOpposite e (.mk γ) = .op g :=
  hp.toMultiplicative.fundamentalGroupToMulOpposite_apply_mk_eq hpΓ Γ_0 Γ_1

theorem fundamentalGroupEquiv_eq [SimplyConnectedSpace E] [IsAddCommutative G]
    (e' : p ⁻¹' {x}) : hp.fundamentalGroupEquiv e = hp.fundamentalGroupEquiv e' := by
  let : IsMulCommutative (Multiplicative G) := ⟨⟨fun a b =>
    congrArg Multiplicative.ofAdd (add_comm' a.toAdd b.toAdd)⟩⟩
  exact
  hp.toMultiplicative.fundamentalGroupEquiv_eq e e'

end IsAddQuotientCoveringMap

namespace AddCircle

variable (p : ℝ)

/-- The loop in `AddCircle p` based at `x` that winds `n` times, defined as
`t ↦ n • (t * p) + x`. -/
def zsmulLoop (x : ℝ) (n : ℤ) : Path (x : AddCircle p) x where
  toFun t := n • (t * p : ℝ) + x
  source' := by simp
  target' := by simp [coe_period]
  continuous_toFun := by fun_prop

@[simp]
theorem zsmulLoop_apply (x : ℝ) (n : ℤ) (t : I) :
    zsmulLoop p x n t = n • (t * p : ℝ) + x :=
  rfl

variable {p} [hp : Fact (0 < p)]

/-- **The fundamental group of the circle is `ℤ`**: the isomorphism sends the class of a loop to
its winding number (`windingNumber_eq_div`). It does not depend on the choice of a lift of the
basepoint (`IsAddQuotientCoveringMap.fundamentalGroupEquiv_eq`). -/
noncomputable def windingNumberIso (x : AddCircle p) :
    FundamentalGroup (AddCircle p) x ≃* Multiplicative ℤ :=
  ((isAddQuotientCoveringMap_coe p).fundamentalGroupEquiv (x := x)
      ⟨(equivIco p 0 x : ℝ), coe_equivIco⟩).trans <|
    MulOpposite.opMulEquiv.symm.trans (AddSubgroup.zmultiplesEquivInt hp.out.ne').toMultiplicative

/-- The winding number of a loop in `AddCircle p`, defined as its image under `windingNumberIso`. -/
noncomputable def windingNumber {x : AddCircle p} (γ : FundamentalGroup (AddCircle p) x) : ℤ :=
  (windingNumberIso x γ).toAdd

/-- The winding number of a loop in `AddCircle p` is `(f 1 - f 0) / p`, for any continuous lift
`f` of the loop to `ℝ`. -/
theorem windingNumber_eq_div {x : AddCircle p} (γ : Path x x) (f : C(I, ℝ)) (hf : (↑) ∘ f = γ) :
    (windingNumber (.mk γ) : ℝ) = (f 1 - f 0) / p := by
  have h0 : (f 0 : AddCircle p) = x := congr($hf 0).trans γ.source
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n • p = f 1 - f 0 :=
    AddSubgroup.mem_zmultiples_iff.mp <| QuotientAddGroup.eq_iff_sub_mem.mp <|
      congr($hf 1).trans <| γ.target.trans h0.symm
  have h : (isAddQuotientCoveringMap_coe p).fundamentalGroupEquiv (x := x) ⟨f 0, h0⟩ (.mk γ) =
      .op (.ofAdd ⟨n • p, n, rfl⟩) :=
    (isAddQuotientCoveringMap_coe p).fundamentalGroupToMulOpposite_apply_mk_eq hf rfl (by simp [hn])
  simp [windingNumber, windingNumberIso, AddSubgroup.zmultiplesEquivInt_apply_zsmul hp.out.ne' n,
    (isAddQuotientCoveringMap_coe p).fundamentalGroupEquiv_eq _ ⟨f 0, h0⟩, h,
    eq_div_iff hp.out.ne', ← zsmul_eq_mul, ← hn]

/-- The loop `t ↦ n • (t * p) + x` has winding number `n`. -/
theorem windingNumber_zsmulLoop (x : ℝ) (n : ℤ) :
    windingNumber (x := x) (.mk (zsmulLoop p x n)) = n := by
  simpa [hp.out.ne'] using windingNumber_eq_div (zsmulLoop p x n)
    ⟨fun t ↦ n • (t * p) + x, by fun_prop⟩ rfl

end AddCircle

/-! ## Project-specific concrete circle generator -/

namespace CellAttachment

/-- The standard positively oriented circle loop, `t ↦ exp(2πt)`, based at `1`. -/
def circleGenerator : Path (1 : Circle) 1 where
  toFun t := Circle.exp ((t : ℝ) * (2 * Real.pi))
  source' := by simp
  target' := by simp
  continuous_toFun := by fun_prop

@[simp]
theorem circleGenerator_apply (t : I) :
    circleGenerator t = Circle.exp ((t : ℝ) * (2 * Real.pi)) := rfl

/-- The corresponding homotopy class in the actual fundamental group. -/
def circleGeneratorClass : FundamentalGroup Circle (1 : Circle) :=
  .mk circleGenerator

/-- The complex unit circle fundamental group, identified with the integers by lifting
through the real exponential covering. -/
def circleFundamentalGroupEquivInt :
    FundamentalGroup Circle (1 : Circle) ≃* Multiplicative ℤ :=
  (Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv
    ⟨0, Circle.exp_zero⟩).trans <|
    MulOpposite.opMulEquiv.symm.trans
      (AddSubgroup.zmultiplesEquivInt (by positivity : (2 * Real.pi : ℝ) ≠ 0)).toMultiplicative

@[simp]
theorem circleFundamentalGroupEquivInt_generator :
    circleFundamentalGroupEquivInt circleGeneratorClass = Multiplicative.ofAdd (1 : ℤ) := by
  have h : Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv
      ⟨0, Circle.exp_zero⟩ circleGeneratorClass =
        .op (.ofAdd ⟨(1 : ℤ) • (2 * Real.pi), 1, rfl⟩) := by
    exact Circle.isAddQuotientCoveringMap_exp.fundamentalGroupToMulOpposite_apply_mk_eq
      (Γ := ⟨fun t => (t : ℝ) * (2 * Real.pi), by fun_prop⟩) rfl (by simp) (by simp)
  change Multiplicative.ofAdd
    (AddSubgroup.zmultiplesEquivInt (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      (MulOpposite.unop
        (Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv
          ⟨0, Circle.exp_zero⟩ circleGeneratorClass)).toAdd) = _
  rw [h]
  exact congrArg Multiplicative.ofAdd (AddSubgroup.zmultiplesEquivInt_apply_zsmul
    (by positivity : (2 * Real.pi : ℝ) ≠ 0) 1)

/-- Every actual based homotopy class on the complex unit circle is an integer power of
the standard loop. This is the generator fact needed for attaching two-cells. -/
theorem circleGenerator_generates (γ : FundamentalGroup Circle (1 : Circle)) :
    ∃ n : ℤ, circleGeneratorClass ^ n = γ := by
  refine ⟨(circleFundamentalGroupEquivInt γ).toAdd, ?_⟩
  apply circleFundamentalGroupEquivInt.injective
  rw [map_zpow, circleFundamentalGroupEquivInt_generator]
  change (circleFundamentalGroupEquivInt γ).toAdd • (1 : ℤ) =
    (circleFundamentalGroupEquivInt γ).toAdd
  simp

/-- The cyclic subgroup generated by the standard circle loop is the whole fundamental group. -/
theorem circleGenerator_zpowers_eq_top :
    Subgroup.zpowers circleGeneratorClass = ⊤ := by
  apply top_unique
  intro γ _
  exact circleGenerator_generates γ

/-- `AddCircle (2π)` and the complex unit circle are the same circle model. -/
def additiveCircleIdentification : AddCircle (2 * Real.pi) ≃ₜ Circle :=
  AddCircle.homeomorphCircle'

@[simp]
theorem additiveCircleIdentification_zero :
    additiveCircleIdentification (0 : AddCircle (2 * Real.pi)) = (1 : Circle) := by
  change Circle.exp 0 = 1
  simp

/-- Mapping the additive generator through the standard homeomorphism gives precisely
the standard complex-circle loop, with its basepoints explicitly identified. -/
theorem additiveCircle_generator_identification :
    ((AddCircle.zsmulLoop (2 * Real.pi) 0 1).map
      additiveCircleIdentification.continuous).cast
        additiveCircleIdentification_zero.symm additiveCircleIdentification_zero.symm =
      circleGenerator := by
  apply Path.ext
  funext t
  change AddCircle.homeomorphCircle'
    ((1 : ℤ) • ((t : ℝ) * (2 * Real.pi)) + (0 : ℝ) : ℝ) =
      Circle.exp ((t : ℝ) * (2 * Real.pi))
  simp [AddCircle.homeomorphCircle'_apply_mk]

end CellAttachment
