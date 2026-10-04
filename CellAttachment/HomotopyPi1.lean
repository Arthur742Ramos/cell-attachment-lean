module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

@[expose] public section


/-! # Compatible fundamental-group maps induced by actual homotopy equivalences -/

noncomputable section
namespace CellAttachment
universe u v
open CategoryTheory
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual fundamental-group map of a homotopy equivalence is bijective. -/
theorem homotopyEquivPi1_bijective (e : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    Function.Bijective (FundamentalGroup.map e.toFun x) :=
  (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.map_bijective
    (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk x)

/-- A compatible pi1 equivalence whose underlying map is the actual induced map. -/
def homotopyEquivPi1 (e : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  MulEquiv.ofBijective (FundamentalGroup.map e.toFun x) (homotopyEquivPi1_bijective e x)

@[simp] theorem homotopyEquivPi1_apply (e : ContinuousMap.HomotopyEquiv X Y) (x : X)
    (g : FundamentalGroup X x) : homotopyEquivPi1 e x g = FundamentalGroup.map e.toFun x g := rfl

end CellAttachment
