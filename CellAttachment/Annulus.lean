module

public import CellAttachment.NormalForm
public import CellAttachment.CircleGenerator
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Analysis.Normed.Module.Convex

@[expose] public section


/-! # Genuine open-disk and punctured-open-disk geometry

The punctured open disk retracts to the circle at radius `1/2`, which lies inside
its domain. Normalizing to the radius-one boundary alone would not give a
self-map of the open disk.
-/

noncomputable section
open scoped unitInterval ContinuousMap
namespace CellAttachment

/-- The annular intersection model is the genuine punctured open unit disk. -/
abbrev Annulus := {z : OpenDisk // (z : ℂ) ≠ 0}

/-- The actual complex coordinate on the punctured open disk. -/
def annulusCoordinate : C(Annulus, ℂ) :=
  ⟨fun z => z.1.1, continuous_subtype_val.comp continuous_subtype_val⟩

lemma annulus_norm_pos (z : Annulus) : 0 < ‖annulusCoordinate z‖ :=
  norm_pos_iff.mpr z.property

lemma annulus_norm_lt_one (z : Annulus) : ‖annulusCoordinate z‖ < 1 :=
  z.1.property

/-- Polar normalization into the actual complex unit circle. -/
def annulusPolar : C(Annulus, Circle) where
  toFun z := ⟨(‖annulusCoordinate z‖⁻¹ : ℝ) • annulusCoordinate z, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀]
    exact ne_of_gt (annulus_norm_pos z)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((annulusCoordinate.continuous.norm.inv₀
      (fun z => ne_of_gt (annulus_norm_pos z))).smul annulusCoordinate.continuous)

/-- The radius-half circle lies inside the punctured open disk. -/
def halfCircle : C(Circle, Annulus) where
  toFun z := ⟨⟨(1 / 2 : ℝ) • (z : ℂ), by
    rw [norm_smul, Real.norm_eq_abs, Circle.norm_coe]
    norm_num⟩, smul_ne_zero (by norm_num) (Circle.coe_ne_zero z)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_const : Continuous fun _ : Circle => (1 / 2 : ℝ)).smul
      (continuous_subtype_val : Continuous fun z : Circle => (z : ℂ))

@[simp] lemma annulusCoordinate_halfCircle (z : Circle) :
    annulusCoordinate (halfCircle z) = (1 / 2 : ℝ) • (z : ℂ) := rfl

@[simp] lemma annulus_norm_halfCircle (z : Circle) :
    ‖annulusCoordinate (halfCircle z)‖ = (1 / 2 : ℝ) := by
  rw [annulusCoordinate_halfCircle, norm_smul, Real.norm_eq_abs, Circle.norm_coe]
  norm_num

@[simp] lemma annulusPolar_halfCircle (z : Circle) : annulusPolar (halfCircle z) = z := by
  apply Subtype.ext
  change ‖annulusCoordinate (halfCircle z)‖⁻¹ • ((1 / 2 : ℝ) • (z : ℂ)) = _
  rw [annulus_norm_halfCircle, smul_smul]
  norm_num

/-- The coefficient interpolating the original radius and radius one half. -/
def annulusRadialCoefficient (t : unitInterval) (z : Annulus) : ℝ :=
  (1 - (t : ℝ)) + (t : ℝ) * (1 / 2) * ‖annulusCoordinate z‖⁻¹

lemma annulusRadialCoefficient_mul_norm (t : unitInterval) (z : Annulus) :
    annulusRadialCoefficient t z * ‖annulusCoordinate z‖ =
      (1 - (t : ℝ)) * ‖annulusCoordinate z‖ + (t : ℝ) * (1 / 2) := by
  unfold annulusRadialCoefficient
  rw [add_mul, mul_assoc, inv_mul_cancel₀ (ne_of_gt (annulus_norm_pos z)), mul_one]

lemma annulusRadialCoefficient_pos (t : unitInterval) (z : Annulus) :
    0 < annulusRadialCoefficient t z := by
  have hi : 0 < ‖annulusCoordinate z‖⁻¹ := inv_pos.mpr (annulus_norm_pos z)
  have ht0 := t.property.1
  have ht1 := t.property.2
  unfold annulusRadialCoefficient
  by_cases h : (t : ℝ) = 1
  · rw [h]
    positivity
  · have hlt : (t : ℝ) < 1 := lt_of_le_of_ne ht1 h
    have hnonneg : 0 ≤ (t : ℝ) * (1 / 2) * ‖annulusCoordinate z‖⁻¹ := by positivity
    linarith

lemma annulusRadialCoefficient_mul_norm_lt_one (t : unitInterval) (z : Annulus) :
    annulusRadialCoefficient t z * ‖annulusCoordinate z‖ < 1 := by
  rw [annulusRadialCoefficient_mul_norm]
  have ht0 := t.property.1
  have ht1 := t.property.2
  by_cases h : (t : ℝ) = 1
  · rw [h]
    norm_num
  · have hlt : (t : ℝ) < 1 := lt_of_le_of_ne ht1 h
    have hm := mul_lt_mul_of_pos_left (annulus_norm_lt_one z) (by linarith : 0 < 1 - (t : ℝ))
    nlinarith

/-- Explicit radial deformation within the actual punctured open disk. -/
def annulusRadialDeformation (t : unitInterval) (z : Annulus) : Annulus :=
  ⟨⟨annulusRadialCoefficient t z • annulusCoordinate z, by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (annulusRadialCoefficient_pos t z)]
      exact annulusRadialCoefficient_mul_norm_lt_one t z⟩,
    smul_ne_zero (ne_of_gt (annulusRadialCoefficient_pos t z)) z.property⟩

lemma annulusRadialDeformation_continuous :
    Continuous (fun p : unitInterval × Annulus => annulusRadialDeformation p.1 p.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous ((fun p : unitInterval × Annulus => annulusRadialCoefficient p.1 p.2) •
    (fun p : unitInterval × Annulus => annulusCoordinate p.2))
  apply Continuous.smul
  · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
      (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
        ((annulusCoordinate.continuous.comp continuous_snd).norm.inv₀
          (fun p => ne_of_gt (annulus_norm_pos p.2))))
  · exact annulusCoordinate.continuous.comp continuous_snd

@[simp] lemma annulusRadialDeformation_zero (z : Annulus) :
    annulusRadialDeformation 0 z = z := by
  apply Subtype.ext
  apply Subtype.ext
  simp [annulusRadialDeformation, annulusRadialCoefficient, annulusCoordinate]

@[simp] lemma annulusRadialDeformation_one (z : Annulus) :
    annulusRadialDeformation 1 z = halfCircle (annulusPolar z) := by
  apply Subtype.ext
  apply Subtype.ext
  change annulusRadialCoefficient 1 z • annulusCoordinate z =
    (1 / 2 : ℝ) • (‖annulusCoordinate z‖⁻¹ • annulusCoordinate z)
  simp [annulusRadialCoefficient, mul_assoc]

/-- The radius-half circle is fixed throughout the deformation. -/
lemma annulusRadialDeformation_halfCircle (t : unitInterval) (z : Circle) :
    annulusRadialDeformation t (halfCircle z) = halfCircle z := by
  apply Subtype.ext
  apply Subtype.ext
  change annulusRadialCoefficient t (halfCircle z) • annulusCoordinate (halfCircle z) =
    annulusCoordinate (halfCircle z)
  have hc : annulusRadialCoefficient t (halfCircle z) = 1 := by
    unfold annulusRadialCoefficient
    rw [annulus_norm_halfCircle]
    ring
  rw [hc, one_smul]

/-- The explicit homotopy from the identity to the half-radius polar projection. -/
def annulusRadialHomotopy :
    (ContinuousMap.id Annulus).Homotopy (halfCircle.comp annulusPolar) where
  toFun p := annulusRadialDeformation p.1 p.2
  continuous_toFun := annulusRadialDeformation_continuous
  map_zero_left := annulusRadialDeformation_zero
  map_one_left := annulusRadialDeformation_one

/-- Polar projection and the half-radius embedding give a genuine homotopy equivalence. -/
def annulusHomotopyEquivCircle : Annulus ≃ₕ Circle where
  toFun := annulusPolar
  invFun := halfCircle
  left_inv := ⟨annulusRadialHomotopy.symm⟩
  right_inv := by
    have h : annulusPolar.comp halfCircle = ContinuousMap.id Circle := by
      apply ContinuousMap.ext
      exact annulusPolar_halfCircle
    rw [h]

/-- Path-connectedness transfers along the explicit homotopy equivalence. -/
theorem homotopyEquivPathConnectedSpace {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace Y] (e : X ≃ₕ Y) :
    PathConnectedSpace X where
  nonempty := ⟨e.invFun (Classical.arbitrary Y)⟩
  joined x y := ⟨((e.left_inv.some.evalAt x).symm.trans
    ((PathConnectedSpace.somePath (e x) (e y)).map e.invFun.continuous)).trans
      (e.left_inv.some.evalAt y)⟩

/-- The annulus is path connected by radial paths and paths on the radius-half circle. -/
instance annulus_pathConnectedSpace : PathConnectedSpace Annulus :=
  homotopyEquivPathConnectedSpace annulusHomotopyEquivCircle

/-- A homotopy equivalence induces the actual map on based fundamental groups
as a multiplicative equivalence. Its forward map is not an abstract choice. -/
def homotopyEquivFundamentalGroup {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) : FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk x)

@[simp] lemma homotopyEquivFundamentalGroup_apply {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (x : X)
    (γ : FundamentalGroup X x) :
    homotopyEquivFundamentalGroup e x γ = FundamentalGroup.map e.toFun x γ := rfl

/-- The based version with the target basepoint explicitly identified. -/
def homotopyEquivFundamentalGroupOfEq {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) {x : X} {y : Y} (h : e x = y) :
    FundamentalGroup X x ≃* FundamentalGroup Y y :=
  (homotopyEquivFundamentalGroup e x).trans
    (CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk h)).conj

@[simp] lemma homotopyEquivFundamentalGroupOfEq_apply {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) {x : X} {y : Y} (h : e x = y)
    (γ : FundamentalGroup X x) :
    homotopyEquivFundamentalGroupOfEq e h γ = FundamentalGroup.mapOfEq e.toFun h γ := rfl

/-- The explicit radius-half basepoint of the annulus. -/
def annulusBasepoint : Annulus := halfCircle 1

@[simp] lemma annulusPolar_basepoint : annulusPolar annulusBasepoint = 1 :=
  annulusPolar_halfCircle 1

/-- The genuine based fundamental group isomorphism induced by polar normalization. -/
def annulusFundamentalGroupEquivCircle :
    FundamentalGroup Annulus annulusBasepoint ≃* FundamentalGroup Circle (1 : Circle) :=
  homotopyEquivFundamentalGroupOfEq annulusHomotopyEquivCircle annulusPolar_basepoint

@[simp] lemma annulusFundamentalGroupEquivCircle_apply
    (γ : FundamentalGroup Annulus annulusBasepoint) :
    annulusFundamentalGroupEquivCircle γ =
      FundamentalGroup.mapOfEq annulusPolar annulusPolar_basepoint γ := rfl

/-- The concrete loop `t ↦ (1/2) exp(2πt)` in the annulus. -/
def annulusGenerator : Path annulusBasepoint annulusBasepoint :=
  circleGenerator.map halfCircle.continuous

/-- The homotopy class of the concrete radius-half positive circle. -/
def annulusGeneratorClass : FundamentalGroup Annulus annulusBasepoint :=
  .mk annulusGenerator

@[simp] lemma annulusGenerator_coordinate (t : unitInterval) :
    annulusCoordinate (annulusGenerator t) =
      (1 / 2 : ℝ) • (Circle.exp ((t : ℝ) * (2 * Real.pi)) : ℂ) := rfl

/-- Polar projection identifies the half-radius generator with the standard generator. -/
lemma annulusPolar_generator :
    (annulusGenerator.map annulusPolar.continuous).cast
      annulusPolar_basepoint.symm annulusPolar_basepoint.symm = circleGenerator := by
  apply Path.ext
  funext t
  exact annulusPolar_halfCircle (circleGenerator t)

@[simp] lemma annulusFundamentalGroupEquivCircle_generator :
    annulusFundamentalGroupEquivCircle annulusGeneratorClass = circleGeneratorClass := by
  rw [annulusFundamentalGroupEquivCircle_apply, FundamentalGroup.mapOfEq_apply]
  change Path.Homotopic.Quotient.mk
    ((annulusGenerator.map annulusPolar.continuous).cast
      annulusPolar_basepoint.symm annulusPolar_basepoint.symm) = _
  rw [annulusPolar_generator]
  rfl

/-- Every actual based annulus class is an integer power of the explicit half-radius loop. -/
theorem annulusGenerator_generates (γ : FundamentalGroup Annulus annulusBasepoint) :
    ∃ n : ℤ, annulusGeneratorClass ^ n = γ := by
  obtain ⟨n, hn⟩ := circleGenerator_generates (annulusFundamentalGroupEquivCircle γ)
  refine ⟨n, annulusFundamentalGroupEquivCircle.injective ?_⟩
  rw [map_zpow, annulusFundamentalGroupEquivCircle_generator]
  exact hn

/-- The concrete annulus loop generates the whole actual fundamental group. -/
theorem annulusGenerator_zpowers_eq_top : Subgroup.zpowers annulusGeneratorClass = ⊤ := by
  apply top_unique
  intro γ _
  exact annulusGenerator_generates γ

/-- Winding numbers give an actual isomorphism of the annulus fundamental group with ℤ. -/
def annulusFundamentalGroupEquivInt :
    FundamentalGroup Annulus annulusBasepoint ≃* Multiplicative ℤ :=
  annulusFundamentalGroupEquivCircle.trans circleFundamentalGroupEquivInt

@[simp] theorem annulusFundamentalGroupEquivInt_generator :
    annulusFundamentalGroupEquivInt annulusGeneratorClass = Multiplicative.ofAdd (1 : ℤ) := by
  change circleFundamentalGroupEquivInt
    (annulusFundamentalGroupEquivCircle annulusGeneratorClass) = _
  rw [annulusFundamentalGroupEquivCircle_generator]
  exact circleFundamentalGroupEquivInt_generator

/-- The coordinate-defined open disk is exactly the ordinary convex metric ball. -/
lemma openDisk_eq_ball : {z : ℂ | ‖z‖ < 1} = Metric.ball (0 : ℂ) 1 := by
  ext z
  simp [Metric.mem_ball, dist_zero_right]

/-- Contractibility comes from actual convex ball geometry. -/
instance openDisk_contractibleSpace : ContractibleSpace OpenDisk := by
  have hc : Convex ℝ {z : ℂ | ‖z‖ < 1} := by
    rw [openDisk_eq_ball]
    exact convex_ball (0 : ℂ) 1
  exact hc.contractibleSpace ⟨0, by simp⟩

/-- In particular the genuine open disk is simply connected. -/
instance openDisk_simplyConnectedSpace : SimplyConnectedSpace OpenDisk := inferInstance

end CellAttachment
