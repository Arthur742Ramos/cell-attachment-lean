module

public import Lean4.path_descent_helpers
public import ClassicalSVK.Bridge.Iso

@[expose] public section


set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open CategoryTheory.Limits
open scoped unitInterval FundamentalCategory

universe u

namespace ClassicalSVK

theorem classicalOpenCoverPushout
    {X : Type u} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) :
    let i₁ : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of U :=
      TopCat.ofHom ⟨(fun x => (⟨x.1, x.2.1⟩ : U)),
        Continuous.subtype_mk continuous_subtype_val (fun x => x.2.1)⟩
    let i₂ : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of V :=
      TopCat.ofHom ⟨(fun x => (⟨x.1, x.2.2⟩ : V)),
        Continuous.subtype_mk continuous_subtype_val (fun x => x.2.2)⟩
    let j₁ : TopCat.of U ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let j₂ : TopCat.of V ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    IsPushout
      (Grpd.forgetToCat.map (FundamentalGroupoid.fundamentalGroupoidFunctor.map i₁))
      (Grpd.forgetToCat.map (FundamentalGroupoid.fundamentalGroupoidFunctor.map i₂))
      (Grpd.forgetToCat.map (FundamentalGroupoid.fundamentalGroupoidFunctor.map j₁))
      (Grpd.forgetToCat.map (FundamentalGroupoid.fundamentalGroupoidFunctor.map j₂)) := by
  dsimp only
  letI : Preorder X := universalPreorder X
  letI : DirectedSpace X := DirectedSpace.Preorder X
  let i₁ : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of U :=
    TopCat.ofHom ⟨(fun x => (⟨x.1, x.2.1⟩ : U)),
      Continuous.subtype_mk continuous_subtype_val (fun x => x.2.1)⟩
  let i₂ : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of V :=
    TopCat.ofHom ⟨(fun x => (⟨x.1, x.2.2⟩ : V)),
      Continuous.subtype_mk continuous_subtype_val (fun x => x.2.2)⟩
  let j₁ : TopCat.of U ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let j₂ : TopCat.of V ⟶ TopCat.of X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let dI0_1 : dTopCat.of (U ∩ V : Set X) ⟶ dTopCat.of (U : Set X) :=
    dTopCat.DirectedSubsetHom (X := dTopCat.of X) (Y₀ := U ∩ V) (Y₁ := U) Set.inter_subset_left
  let dI0_2 : dTopCat.of (U ∩ V : Set X) ⟶ dTopCat.of (V : Set X) :=
    dTopCat.DirectedSubsetHom (X := dTopCat.of X) (Y₀ := U ∩ V) (Y₁ := V) Set.inter_subset_right
  let dJ0_1 : dTopCat.of (U : Set X) ⟶ dTopCat.of X := dTopCat.DirectedSubtypeHom (X := dTopCat.of X) U
  let dJ0_2 : dTopCat.of (V : Set X) ⟶ dTopCat.of X := dTopCat.DirectedSubtypeHom (X := dTopCat.of X) V
  have hi₁ : i₁ = TopCat.ofHom dI0_1.toContinuousMap := by
    ext x
    rfl
  have hi₂ : i₂ = TopCat.ofHom dI0_2.toContinuousMap := by
    ext x
    rfl
  have hj₁ : j₁ = TopCat.ofHom dJ0_1.toContinuousMap := by
    ext x
    rfl
  have hj₂ : j₂ = TopCat.ofHom dJ0_2.toContinuousMap := by
    ext x
    rfl
  let dI₁ := FundamentalCategory.fundamentalCategoryFunctor.map dI0_1
  let dI₂ := FundamentalCategory.fundamentalCategoryFunctor.map dI0_2
  let dJ₁ := FundamentalCategory.fundamentalCategoryFunctor.map dJ0_1
  let dJ₂ := FundamentalCategory.fundamentalCategoryFunctor.map dJ0_2
  let cI₁ := Grpd.forgetToCat.map (FundamentalGroupoid.fundamentalGroupoidFunctor.map i₁)
  let cI₂ := Grpd.forgetToCat.map (FundamentalGroupoid.fundamentalGroupoidFunctor.map i₂)
  let cJ₁ := Grpd.forgetToCat.map (FundamentalGroupoid.fundamentalGroupoidFunctor.map j₁)
  let cJ₂ := Grpd.forgetToCat.map (FundamentalGroupoid.fundamentalGroupoidFunctor.map j₂)
  let dToP_I : FundamentalCategory {x : X // x ∈ U ∩ V} ⥤ Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of {x : X // x ∈ U ∩ V})) := directedToClassical (X := {x : X // x ∈ U ∩ V})
  let dToP_U : FundamentalCategory U ⥤ Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of U)) := directedToClassical (X := U)
  let dToP_V : FundamentalCategory V ⥤ Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of V)) := directedToClassical (X := V)
  let dToP_X : FundamentalCategory X ⥤ Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)) := directedToClassical (X := X)
  let pToD_I : Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of {x : X // x ∈ U ∩ V})) ⥤ FundamentalCategory {x : X // x ∈ U ∩ V} := classicalToDirected (X := {x : X // x ∈ U ∩ V})
  let pToD_U : Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of U)) ⥤ FundamentalCategory U := classicalToDirected (X := U)
  let pToD_V : Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of V)) ⥤ FundamentalCategory V := classicalToDirected (X := V)
  let pToD_X : Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)) ⥤ FundamentalCategory X := classicalToDirected (X := X)
  let dToP_I_cat : FundamentalCategory.fundamentalCategoryFunctor.obj (dTopCat.of {x : X // x ∈ U ∩ V}) ⟶ Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of {x : X // x ∈ U ∩ V})) := ⟨dToP_I⟩
  let dToP_U_cat : FundamentalCategory.fundamentalCategoryFunctor.obj (dTopCat.of U) ⟶ Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of U)) := ⟨dToP_U⟩
  let dToP_V_cat : FundamentalCategory.fundamentalCategoryFunctor.obj (dTopCat.of V) ⟶ Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of V)) := ⟨dToP_V⟩
  let dToP_X_cat : FundamentalCategory.fundamentalCategoryFunctor.obj (dTopCat.of X) ⟶ Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)) := ⟨dToP_X⟩
  let pToD_I_cat : Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of {x : X // x ∈ U ∩ V})) ⟶ FundamentalCategory.fundamentalCategoryFunctor.obj (dTopCat.of {x : X // x ∈ U ∩ V}) := ⟨pToD_I⟩
  let pToD_U_cat : Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of U)) ⟶ FundamentalCategory.fundamentalCategoryFunctor.obj (dTopCat.of U) := ⟨pToD_U⟩
  let pToD_V_cat : Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of V)) ⟶ FundamentalCategory.fundamentalCategoryFunctor.obj (dTopCat.of V) := ⟨pToD_V⟩
  let pToD_X_cat : Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)) ⟶ FundamentalCategory.fundamentalCategoryFunctor.obj (dTopCat.of X) := ⟨pToD_X⟩
  have hi₁_nat : dI₁ ≫ dToP_U_cat = dToP_I_cat ≫ cI₁ := by
    apply Cat.ext
    dsimp [dI₁, dToP_U_cat, dToP_I_cat, cI₁, dToP_U, dToP_I]
    simpa only [← hi₁] using directedToClassical_naturality dI0_1
  have hi₂_nat : dI₂ ≫ dToP_V_cat = dToP_I_cat ≫ cI₂ := by
    apply Cat.ext
    dsimp [dI₂, dToP_V_cat, dToP_I_cat, cI₂, dToP_V, dToP_I]
    simpa only [← hi₂] using directedToClassical_naturality dI0_2
  have hj₁_nat : dJ₁ ≫ dToP_X_cat = dToP_U_cat ≫ cJ₁ := by
    apply Cat.ext
    dsimp [dJ₁, dToP_X_cat, dToP_U_cat, cJ₁, dToP_X, dToP_U]
    simpa only [← hj₁] using directedToClassical_naturality dJ0_1
  have hj₂_nat : dJ₂ ≫ dToP_X_cat = dToP_V_cat ≫ cJ₂ := by
    apply Cat.ext
    dsimp [dJ₂, dToP_X_cat, dToP_V_cat, cJ₂, dToP_X, dToP_V]
    simpa only [← hj₂] using directedToClassical_naturality dJ0_2
  have hi₁_nat' : cI₁ ≫ pToD_U_cat = pToD_I_cat ≫ dI₁ := by
    apply Cat.ext
    dsimp [dI₁, cI₁, pToD_U_cat, pToD_I_cat, pToD_U, pToD_I]
    simpa only [← hi₁] using classicalToDirected_naturality dI0_1
  have hi₂_nat' : cI₂ ≫ pToD_V_cat = pToD_I_cat ≫ dI₂ := by
    apply Cat.ext
    dsimp [dI₂, cI₂, pToD_V_cat, pToD_I_cat, pToD_V, pToD_I]
    simpa only [← hi₂] using classicalToDirected_naturality dI0_2
  have hj₁_nat' : cJ₁ ≫ pToD_X_cat = pToD_U_cat ≫ dJ₁ := by
    apply Cat.ext
    dsimp [dJ₁, cJ₁, pToD_X_cat, pToD_U_cat, pToD_X, pToD_U]
    simpa only [← hj₁] using classicalToDirected_naturality dJ0_1
  have hj₂_nat' : cJ₂ ≫ pToD_X_cat = pToD_V_cat ≫ dJ₂ := by
    apply Cat.ext
    dsimp [dJ₂, cJ₂, pToD_X_cat, pToD_V_cat, pToD_X, pToD_V]
    simpa only [← hj₂] using classicalToDirected_naturality dJ0_2
  have hIsoI : pToD_I_cat ≫ dToP_I_cat = 𝟙 _ := by
    apply Cat.ext
    exact classicalToDirected_comp_directedToClassical
      (X := {x : X // x ∈ U ∩ V})
  have hIsoU : pToD_U_cat ≫ dToP_U_cat = 𝟙 _ := by
    apply Cat.ext
    exact classicalToDirected_comp_directedToClassical (X := U)
  have hIsoV : pToD_V_cat ≫ dToP_V_cat = 𝟙 _ := by
    apply Cat.ext
    exact classicalToDirected_comp_directedToClassical (X := V)
  have hIsoX : pToD_X_cat ≫ dToP_X_cat = 𝟙 _ := by
    apply Cat.ext
    exact classicalToDirected_comp_directedToClassical (X := X)
  have hpathDescent : IsPushout dI₁ dI₂ dJ₁ dJ₂ := by
    -- Construct the descent functor directly. Its action on each path is
    -- defined by an open-cover subdivision; independence of the subdivision
    -- and of the path-homotopy representative is established by the interval
    -- and square subdivision lemmas in `PushoutFunctor`.
    apply PushoutAlternative.isPushout_alternative
    · rw [← Functor.map_comp, ← Functor.map_comp]
      change FundamentalCategory.fundamentalCategoryFunctor.map (dI0_1 ≫ dJ0_1) =
        FundamentalCategory.fundamentalCategoryFunctor.map (dI0_2 ≫ dJ0_2)
      congr 1
    intro C F₁ F₂ h_comm
    let descent := DirectedVanKampen.PushoutFunctor.Functor hUV hU hV h_comm
    use descent
    constructor
    constructor
    · exact DirectedVanKampen.PushoutFunctor.functor_comp_left hUV hU hV h_comm
    · exact DirectedVanKampen.PushoutFunctor.functor_comp_right hUV hU hV h_comm
    · rintro F' ⟨h₁, h₂⟩
      exact DirectedVanKampen.PushoutFunctor.functor_uniq hUV hU hV h_comm F' h₁ h₂
  have hcomm : cI₁ ≫ cJ₁ = cI₂ ≫ cJ₂ := by
    calc
      cI₁ ≫ cJ₁ = (pToD_I_cat ≫ dToP_I_cat) ≫ (cI₁ ≫ cJ₁) := by
        rw [hIsoI]
        simp
      _ = pToD_I_cat ≫ ((dToP_I_cat ≫ cI₁) ≫ cJ₁) := by simp [Category.assoc]
      _ = pToD_I_cat ≫ ((dI₁ ≫ dToP_U_cat) ≫ cJ₁) := by rw [← hi₁_nat]
      _ = pToD_I_cat ≫ (dI₁ ≫ (dToP_U_cat ≫ cJ₁)) := by simp [Category.assoc]
      _ = pToD_I_cat ≫ (dI₁ ≫ (dJ₁ ≫ dToP_X_cat)) := by rw [← hj₁_nat]
      _ = pToD_I_cat ≫ ((dI₁ ≫ dJ₁) ≫ dToP_X_cat) := by simp [Category.assoc]
      _ = pToD_I_cat ≫ ((dI₂ ≫ dJ₂) ≫ dToP_X_cat) := by
        exact congrArg (fun f => pToD_I_cat ≫ f ≫ dToP_X_cat) hpathDescent.w
      _ = pToD_I_cat ≫ (dI₂ ≫ (dJ₂ ≫ dToP_X_cat)) := by simp [Category.assoc]
      _ = pToD_I_cat ≫ (dI₂ ≫ (dToP_V_cat ≫ cJ₂)) := by rw [hj₂_nat]
      _ = pToD_I_cat ≫ ((dI₂ ≫ dToP_V_cat) ≫ cJ₂) := by simp [Category.assoc]
      _ = pToD_I_cat ≫ ((dToP_I_cat ≫ cI₂) ≫ cJ₂) := by rw [hi₂_nat]
      _ = (pToD_I_cat ≫ dToP_I_cat) ≫ (cI₂ ≫ cJ₂) := by simp [Category.assoc]
      _ = cI₂ ≫ cJ₂ := by
        rw [hIsoI]
        simp
  let cP : PushoutCocone cI₁ cI₂ := PushoutCocone.mk cJ₁ cJ₂ hcomm
  let toDirectedCocone : PushoutCocone cI₁ cI₂ → PushoutCocone dI₁ dI₂ := fun s =>
    PushoutCocone.mk (dToP_U_cat ≫ s.inl) (dToP_V_cat ≫ s.inr) (by
      calc
        dI₁ ≫ (dToP_U_cat ≫ s.inl) = (dI₁ ≫ dToP_U_cat) ≫ s.inl := by simp [Category.assoc]
        _ = (dToP_I_cat ≫ cI₁) ≫ s.inl := by rw [hi₁_nat]
        _ = dToP_I_cat ≫ (cI₁ ≫ s.inl) := by simp [Category.assoc]
        _ = dToP_I_cat ≫ (cI₂ ≫ s.inr) := by exact congrArg (fun f => dToP_I_cat ≫ f) s.condition
        _ = (dToP_I_cat ≫ cI₂) ≫ s.inr := by simp [Category.assoc]
        _ = (dI₂ ≫ dToP_V_cat) ≫ s.inr := by rw [← hi₂_nat]
        _ = dI₂ ≫ (dToP_V_cat ≫ s.inr) := by simp [Category.assoc])
  let liftDesc : ∀ s : PushoutCocone cI₁ cI₂,
      Grpd.forgetToCat.obj (FundamentalGroupoid.fundamentalGroupoidFunctor.obj (TopCat.of X)) ⟶ s.pt := fun s => by
    exact pToD_X_cat ≫ PushoutCocone.IsColimit.desc hpathDescent.isColimit
      (toDirectedCocone s).inl (toDirectedCocone s).inr (toDirectedCocone s).condition
  have hcolim : IsColimit cP := by
    change IsColimit (PushoutCocone.mk cJ₁ cJ₂ hcomm)
    refine PushoutCocone.IsColimit.mk (f := cI₁) (g := cI₂) (inl := cJ₁) (inr := cJ₂) hcomm liftDesc ?_ ?_ ?_
    · intro s
      let desc := PushoutCocone.IsColimit.desc hpathDescent.isColimit (toDirectedCocone s).inl (toDirectedCocone s).inr (toDirectedCocone s).condition
      calc
        cJ₁ ≫ liftDesc s = cJ₁ ≫ (pToD_X_cat ≫ desc) := rfl
        _ = (cJ₁ ≫ pToD_X_cat) ≫ desc := by simp [Category.assoc]
        _ = (pToD_U_cat ≫ dJ₁) ≫ desc := by rw [hj₁_nat']
        _ = pToD_U_cat ≫ (dJ₁ ≫ desc) := by simp [Category.assoc]
        _ = pToD_U_cat ≫ ((toDirectedCocone s).inl) := by
          exact congrArg (fun f => pToD_U_cat ≫ f)
            (PushoutCocone.IsColimit.inl_desc hpathDescent.isColimit (toDirectedCocone s).inl (toDirectedCocone s).inr (toDirectedCocone s).condition)
        _ = (pToD_U_cat ≫ dToP_U_cat) ≫ s.inl := by simp [toDirectedCocone, Category.assoc]
        _ = s.inl := by rw [hIsoU]; simp
    · intro s
      let desc := PushoutCocone.IsColimit.desc hpathDescent.isColimit (toDirectedCocone s).inl (toDirectedCocone s).inr (toDirectedCocone s).condition
      calc
        cJ₂ ≫ liftDesc s = cJ₂ ≫ (pToD_X_cat ≫ desc) := rfl
        _ = (cJ₂ ≫ pToD_X_cat) ≫ desc := by simp [Category.assoc]
        _ = (pToD_V_cat ≫ dJ₂) ≫ desc := by rw [hj₂_nat']
        _ = pToD_V_cat ≫ (dJ₂ ≫ desc) := by simp [Category.assoc]
        _ = pToD_V_cat ≫ ((toDirectedCocone s).inr) := by
          exact congrArg (fun f => pToD_V_cat ≫ f)
            (PushoutCocone.IsColimit.inr_desc hpathDescent.isColimit (toDirectedCocone s).inl (toDirectedCocone s).inr (toDirectedCocone s).condition)
        _ = (pToD_V_cat ≫ dToP_V_cat) ≫ s.inr := by simp [toDirectedCocone, Category.assoc]
        _ = s.inr := by rw [hIsoV]; simp
    · intro s m hm₁ hm₂
      let desc := PushoutCocone.IsColimit.desc hpathDescent.isColimit (toDirectedCocone s).inl (toDirectedCocone s).inr (toDirectedCocone s).condition
      have hmap : dToP_X_cat ≫ m = desc := by
        have hleft : dJ₁ ≫ (dToP_X_cat ≫ m) = dJ₁ ≫ desc := by
          calc
            dJ₁ ≫ (dToP_X_cat ≫ m) = (dJ₁ ≫ dToP_X_cat) ≫ m := by simp [Category.assoc]
            _ = (dToP_U_cat ≫ cJ₁) ≫ m := by rw [hj₁_nat]
            _ = dToP_U_cat ≫ (cJ₁ ≫ m) := by simp [Category.assoc]
            _ = dToP_U_cat ≫ s.inl := by exact congrArg (fun f => dToP_U_cat ≫ f) hm₁
            _ = dJ₁ ≫ desc := by
              exact (PushoutCocone.IsColimit.inl_desc hpathDescent.isColimit (toDirectedCocone s).inl (toDirectedCocone s).inr (toDirectedCocone s).condition).symm
        have hright : dJ₂ ≫ (dToP_X_cat ≫ m) = dJ₂ ≫ desc := by
          calc
            dJ₂ ≫ (dToP_X_cat ≫ m) = (dJ₂ ≫ dToP_X_cat) ≫ m := by simp [Category.assoc]
            _ = (dToP_V_cat ≫ cJ₂) ≫ m := by rw [hj₂_nat]
            _ = dToP_V_cat ≫ (cJ₂ ≫ m) := by simp [Category.assoc]
            _ = dToP_V_cat ≫ s.inr := by exact congrArg (fun f => dToP_V_cat ≫ f) hm₂
            _ = dJ₂ ≫ desc := by
              exact (PushoutCocone.IsColimit.inr_desc hpathDescent.isColimit (toDirectedCocone s).inl (toDirectedCocone s).inr (toDirectedCocone s).condition).symm
        exact PushoutCocone.IsColimit.hom_ext hpathDescent.isColimit hleft hright
      calc
        m = 𝟙 _ ≫ m := by simp
        _ = (pToD_X_cat ≫ dToP_X_cat) ≫ m := by rw [hIsoX]
        _ = pToD_X_cat ≫ (dToP_X_cat ≫ m) := by simp [Category.assoc]
        _ = pToD_X_cat ≫ desc := by rw [hmap]
  exact IsPushout.of_isColimit hcolim

end ClassicalSVK
