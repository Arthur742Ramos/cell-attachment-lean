module

public import CellAttachment.Statement
public import CellAttachment.GroupQuotient
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

@[expose] public section


/-! # Attaching relators are actually nullhomotopic in the adjunction quotient -/

noncomputable section
namespace CellAttachment
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- The genuine closed disk is contractible by its ordinary convex geometry. -/
instance disk_contractibleSpace : ContractibleSpace Disk := by
  have hc : Convex ℝ {z : ℂ | ‖z‖ ≤ 1} := by
    have h : {z : ℂ | ‖z‖ ≤ 1} = Metric.closedBall (0 : ℂ) 1 := by
      ext z
      simp [Metric.mem_closedBall, dist_zero_right]
    rw [h]
    exact convex_closedBall (0 : ℂ) 1
  exact hc.contractibleSpace ⟨0, by simp⟩

instance disk_simplyConnectedSpace : SimplyConnectedSpace Disk := inferInstance

/-- The characteristic map on the actual boundary is the actual included attaching map. -/
theorem characteristic_comp_boundary (f : ι → C(Circle, X)) (i : ι) :
    (characteristic f i).comp boundaryInclusion = (inclusion f).comp (f i) := by
  ext z
  exact characteristic_boundary f i z

/-- The once-around attaching loop contracts through its attached closed disk. -/
theorem attachedCircle_nullhomotopic (f : ι → C(Circle, X)) (i : ι) :
    (circleGenerator.map ((inclusion f).comp (f i)).continuous).Homotopic
      (Path.refl (inclusion f (f i 1))) := by
  have h := (SimplyConnectedSpace.paths_homotopic
    (circleGenerator.map boundaryInclusion.continuous)
    (Path.refl (boundaryInclusion 1))).map (characteristic f i)
  have hb := characteristic_boundary f i (1 : Circle)
  have hh := h.pathCast hb.symm hb.symm
  have hl : circleGenerator.map ((inclusion f).comp (f i)).continuous =
      (((circleGenerator.map boundaryInclusion.continuous).map (characteristic f i).continuous).cast hb.symm hb.symm) := by
    apply Path.ext
    funext t
    exact (characteristic_boundary f i (circleGenerator t)).symm
  have hr : Path.refl (inclusion f (f i 1)) =
      (((Path.refl (boundaryInclusion 1)).map (characteristic f i).continuous).cast hb.symm hb.symm) := by
    apply Path.ext
    funext t
    exact hb.symm
  rw [hl,hr]
  exact hh

/-- Each chosen whiskered relator is killed by the actual inclusion-induced map. -/
theorem inclusionPi1_attachingLoopClass (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) (i : ι) :
    inclusionPi1 f x₀ (attachingLoopClass f x₀ γ i) = 1 := by
  have hc : Path.Homotopic.Quotient.mk
      ((circleGenerator.map (f i).continuous).map (inclusion f).continuous) =
        Path.Homotopic.Quotient.refl (inclusion f (f i 1)) := by
    exact Quotient.sound (attachedCircle_nullhomotopic f i)
  change Path.Homotopic.Quotient.mk ((attachingLoop f x₀ γ i).map (inclusion f).continuous) =
    Path.Homotopic.Quotient.refl (inclusion f x₀)
  simp only [attachingLoop, Path.map_trans, Path.map_symm, Path.Homotopic.Quotient.mk_trans]
  rw [hc]
  simp only [Path.Homotopic.Quotient.refl_trans]
  rw [← Path.map_symm, Path.Homotopic.Quotient.mk_symm]
  exact Path.Homotopic.Quotient.trans_symm _

/-- The proved lower kernel inclusion, with no van Kampen or exactness assumption. -/
theorem attachingNormalClosure_le_ker (f : ι → C(Circle, X)) (x₀ : X)
    (γ : ∀ i, Path x₀ (f i 1)) :
    attachingNormalClosure f x₀ γ ≤ (inclusionPi1 f x₀).ker :=
  (normalClosure_range_le_ker_iff _ _).mpr (inclusionPi1_attachingLoopClass f x₀ γ)

end CellAttachment
