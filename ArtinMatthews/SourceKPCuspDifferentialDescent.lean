module

public import ArtinMatthews.SourceKPCuspSobolev
public import Mathlib.Analysis.Calculus.Deriv.Comp


set_option backward.privateInPublic true
@[expose] public section

/-! The basis derivatives of a C1 lift descend to the genuine principal
cusp quotient and give its actual directional derivative fields. -/
namespace ArtinMatthews
open NumberField Module Module.Free Topology
open scoped NumberField ContDiff Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] (d : 𝓞 K) (hd : d ≠ 0)
local notation "E" => mixedEmbedding.mixedSpace K
local notation "Q" => SourceKPCuspPrincipalQuotient K d
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)

theorem sourceKPCusp_directionalDerivative_of_C1_lift (f : C(Q,ℂ))
    (hF : ContDiff ℝ 1 (fun x : E => f (sourceKPCuspArchQuotientMap K d x))) :
    ∃ g : I → C(Q,ℂ), SourceKPCuspDirectionalDerivative K d hd f g ∧
      ∀ i x, g i (sourceKPCuspArchQuotientMap K d x) =
        fderiv ℝ (fun y : E => f (sourceKPCuspArchQuotientMap K d y)) x
          (sourceKPCuspLatticeBasis K d hd i) := by
  let q := sourceKPCuspArchQuotientMap K d
  let F : E → ℂ := fun x => f (q x)
  change ContDiff ℝ 1 F at hF
  have hperiod (x y : E) (hxy : q x = q y) : fderiv ℝ F x = fderiv ℝ F y := by
    let a := y-x
    have ha : q a = 0 := by
      dsimp only [a]
      rw [map_sub,hxy,sub_self]
    have he : (fun u : E => F (u+a)) = F := by
      funext u
      dsimp only [F]
      rw [map_add,ha,add_zero]
    have hya : x+a = y := by dsimp only [a]; abel
    have hy : HasFDerivAt F (fderiv ℝ F y) (x+a) := by
      rw [hya]
      exact (hF.differentiable (by norm_num) y).hasFDerivAt
    have hx : HasFDerivAt (fun u : E => u+a) (ContinuousLinearMap.id ℝ E) x :=
      (hasFDerivAt_id x).add_const a
    have h := hy.comp x hx
    have h' : HasFDerivAt F (fderiv ℝ F y) x := by
      simpa only [Function.comp_def,ContinuousLinearMap.comp_id,he] using h
    exact h'.fderiv
  let D : I → E → ℂ := fun i x => fderiv ℝ F x (sourceKPCuspLatticeBasis K d hd i)
  have hD (i : I) : Continuous (D i) :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hfact (i : I) : (D i).FactorsThrough q := by
    intro x y hxy
    exact congrArg (fun L => L (sourceKPCuspLatticeBasis K d hd i)) (hperiod x y hxy)
  have hq : IsQuotientMap q := (sourceKPCuspArchQuotientMap_isOpenMap K d hd).isQuotientMap
    (sourceKPCuspArchQuotientMap_continuous K d) (sourceKPCuspArchQuotientMap_surjective K d hd)
  have hcont (i : I) : Continuous (Function.extend q (D i) (fun _ => 0)) := by
    apply hq.continuous_iff.mpr
    exact (hD i).congr (fun x => ((hfact i).extend_apply _ x).symm)
  let g : I → C(Q,ℂ) := fun i => ⟨Function.extend q (D i) (fun _ => 0),hcont i⟩
  have hEval (i : I) (x : E) : g i (q x) = D i x := by
    change Function.extend q (D i) (fun _ : Q => 0) (q x) = D i x
    exact (hfact i).extend_apply _ x
  refine ⟨g,?_,hEval⟩
  intro i x t
  let b := sourceKPCuspLatticeBasis K d hd i
  have hline : HasDerivAt (fun u : ℝ => x+u•b) b t := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id t).smul_const b).const_add x
  change HasDerivAt (fun u : ℝ => F (x+u•b)) (g i (q (x+t•b))) t
  rw [hEval]
  exact (hF.differentiable (by norm_num) (x+t•b)).hasFDerivAt.comp_hasDerivAt t hline

end
end ArtinMatthews
