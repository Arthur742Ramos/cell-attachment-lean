import CellAttachment.Adjunction
import Mathlib.Topology.Homotopy.Basic

/-! # Explicit radial deformation of the punctured closed disk -/

noncomputable section
open scoped unitInterval
namespace CellAttachment

abbrev PuncturedDisk := {z : Disk // (z : ℂ) ≠ 0}

/-- The complex coordinate of a punctured disk point. -/
def puncturedCoordinate : C(PuncturedDisk, ℂ) :=
  ⟨fun z => z.1.1, continuous_subtype_val.comp continuous_subtype_val⟩

lemma punctured_norm_pos (z : PuncturedDisk) : 0 < ‖puncturedCoordinate z‖ :=
  norm_pos_iff.mpr z.property

lemma punctured_norm_le_one (z : PuncturedDisk) : ‖puncturedCoordinate z‖ ≤ 1 :=
  z.1.property

/-- Normalize a nonzero disk point to the actual unit circle. -/
def polar : C(PuncturedDisk, Circle) where
  toFun z := ⟨(‖puncturedCoordinate z‖⁻¹ : ℝ) • puncturedCoordinate z, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀]
    exact ne_of_gt (punctured_norm_pos z)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((puncturedCoordinate.continuous.norm.inv₀
      (fun z => ne_of_gt (punctured_norm_pos z))).smul puncturedCoordinate.continuous)

/-- The radial expansion coefficient at a homotopy time. -/
def radialCoefficient (t : unitInterval) (z : PuncturedDisk) : ℝ :=
  (1 - (t : ℝ)) + (t : ℝ) * ‖puncturedCoordinate z‖⁻¹

lemma radialCoefficient_mul_norm (t : unitInterval) (z : PuncturedDisk) :
    radialCoefficient t z * ‖puncturedCoordinate z‖ =
      (1 - (t : ℝ)) * ‖puncturedCoordinate z‖ + (t : ℝ) := by
  unfold radialCoefficient
  rw [add_mul, mul_assoc, inv_mul_cancel₀ (ne_of_gt (punctured_norm_pos z)), mul_one]

lemma radialCoefficient_pos (t : unitInterval) (z : PuncturedDisk) :
    0 < radialCoefficient t z := by
  have hr := punctured_norm_pos z
  have hr1 := punctured_norm_le_one z
  have hm : (t : ℝ) * ‖puncturedCoordinate z‖ ≤ (t : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hr1 t.property.1
  have hprod : 0 < radialCoefficient t z * ‖puncturedCoordinate z‖ := by
    rw [radialCoefficient_mul_norm]
    nlinarith [t.property.1]
  exact (mul_pos_iff_of_pos_right hr).mp hprod

lemma radialCoefficient_mul_norm_le_one (t : unitInterval) (z : PuncturedDisk) :
    radialCoefficient t z * ‖puncturedCoordinate z‖ ≤ 1 := by
  rw [radialCoefficient_mul_norm]
  have h := mul_le_mul_of_nonneg_left (punctured_norm_le_one z)
    (sub_nonneg.mpr t.property.2)
  nlinarith

/-- The radial deformation stays within the genuine punctured closed disk. -/
def radialDeformation (t : unitInterval) (z : PuncturedDisk) : PuncturedDisk :=
  ⟨⟨radialCoefficient t z • puncturedCoordinate z, by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (radialCoefficient_pos t z)]
      exact radialCoefficient_mul_norm_le_one t z⟩,
    smul_ne_zero (ne_of_gt (radialCoefficient_pos t z)) z.property⟩

lemma radialDeformation_continuous :
    Continuous (fun p : unitInterval × PuncturedDisk => radialDeformation p.1 p.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous ((fun p : unitInterval × PuncturedDisk => radialCoefficient p.1 p.2) •
    (fun p : unitInterval × PuncturedDisk => puncturedCoordinate p.2))
  apply Continuous.smul
  · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((puncturedCoordinate.continuous.comp continuous_snd).norm.inv₀
          (fun p => ne_of_gt (punctured_norm_pos p.2))))
  · exact puncturedCoordinate.continuous.comp continuous_snd

@[simp] lemma radialDeformation_zero (z : PuncturedDisk) : radialDeformation 0 z = z := by
  apply Subtype.ext
  apply Subtype.ext
  simp [radialDeformation, radialCoefficient, puncturedCoordinate]

@[simp] lemma radialDeformation_one_coordinate (z : PuncturedDisk) :
    (radialDeformation 1 z).1.1 = (polar z : ℂ) := by
  change radialCoefficient 1 z • puncturedCoordinate z = ‖puncturedCoordinate z‖⁻¹ • puncturedCoordinate z
  simp [radialCoefficient]

/-- Every boundary point stays fixed throughout the radial deformation. -/
lemma radialDeformation_boundary_fixed (t : unitInterval) (z : PuncturedDisk)
    (h : ‖puncturedCoordinate z‖ = 1) : radialDeformation t z = z := by
  apply Subtype.ext
  apply Subtype.ext
  change radialCoefficient t z • puncturedCoordinate z = puncturedCoordinate z
  simp [radialCoefficient, h]

end CellAttachment
