module

public import ArtinMatthews.GiantSignedEdgeColumnTests
public import ArtinMatthews.GiantSignedEdgePairingReal


set_option backward.privateInPublic true
@[expose] public section

/-! The weighted forward test is the original signed edge applied to a
real nonnegative test, with its input degree weight left outside. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {t : J → ℕ}

theorem giantSignedEdgeColumnTest_apply
    (ν : (j : J) → P j → ℝ) (V : J → ℝ) (ρ : ℝ) (d : ℤ) (D : ℕ) (v : ℝ)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (source : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P) :
    giantSignedEdgeCoupledApply ν V ρ d (giantSignedEdgeColumnTest D v f) source m =
      v ^ (∑ j, m.1 j) *
        (giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
          (fun target out => (f target out : ℂ)) m).re := by
  have he : giantSignedEdgeColumnTest (P := P) D v f =
      (fun S T source target old out => v ^ (∑ j, old.1 j) *
        (if GiantSignedEdgePromotionBan D T target then f target out else 0)) := by
    funext S T source target old out
    unfold giantSignedEdgeColumnTest
    split_ifs <;> ring
  rw [he, giantSignedEdgeCoupledApply_input_mul, giantSignedEdgeApply_eq_coe_coupled]
  rfl

theorem giantSignedEdgeApply_ofReal_norm (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (d : ℤ) (D : ℕ)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (hf : ∀ target out, 0 ≤ f target out)
    (source : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P) :
    ‖giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
        (fun target out => (f target out : ℂ)) m‖ =
      (giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
        (fun target out => (f target out : ℂ)) m).re := by
  rw [giantSignedEdgeApply_eq_coe_coupled]
  have hp := giantSignedEdgeCoupledApply_nonneg ν hν V hV hρ d
    (fun _ T _ target _ out => if GiantSignedEdgePromotionBan D T target then f target out else 0)
    (fun _ _ _ target _ out => by
      split_ifs
      · exact hf target out
      · exact le_rfl) source m
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
  rfl

end
end ArtinMatthews
