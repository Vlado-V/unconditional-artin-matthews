module

public import ArtinMatthews.GiantCandidatePrimeRemoval
public import ArtinMatthews.GiantOrdinarySlotReplacementActual


set_option backward.privateInPublic true
@[expose] public section

/-! The two literal replacements in PD07, from the ordered prime tuple
to the stripped rough proxy with the original fixed character. -/

namespace ArtinMatthews
noncomputable section
open Filter Finset
open scoped Asymptotics ContDiff

theorem giant_ordinary_tuple_sub_stripped_isLittleO {J : Type}
    [Fintype J] [DecidableEq J]
    (P : ℝ → Finset ℕ)
    (hP : ∀ᶠ x : ℝ in atTop,∀ p∈P x,p.Prime ∧
      (p:ℝ)≤Real.exp ((Real.log x)^(9/20:ℝ)))
    (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j,(1/10:ℝ)<e j ∧ e j<(1/5:ℝ))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (Φ : ℝ → ℝ) {a T : ℝ} (ha : 0 < a) (hT : 0 < T)
    (hsupp : Function.support Φ ⊆ Set.Icc a T) (hΦ : ContDiff ℝ ∞ Φ)
    (γ : ℝ) (hγ : 0 < γ) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    (j : ℕ) (hj : 2 ≤ j)
    (hdepth : 100*(5*(29+2*(((j-1)*(j-1)+6:ℕ):ℝ))+36) < (Fintype.card J:ℝ)) :
    (fun x => giantOrdinaryTupleSum e χ (giantMarkedCenteredCore ε) Φ T γ j x -
      giantOrdinaryStrippedProxyTupleSum P e χ (giantMarkedCenteredCore ε) Φ T γ j x)
      =o[atTop] (fun x : ℝ => x/Real.log x) := by
  let G := giantMarkedCenteredCore ε
  have hG : ∀ᶠ x : ℝ in atTop,∀ n,‖G x n‖≤1 :=
    (giantMarkedCenteredCore_interface e (fun l => (he l).2.trans (by norm_num)) hε hεq).mono
      (fun _ h => h.1)
  have hslot := giant_ordinary_tuple_proxy_difference_isLittleO e hinj he χ Φ ha hT hsupp hΦ γ hγ
    hε hεq j hj hdepth
  have hstrip := giant_ordinary_proxy_sub_stripped_isLittleO P hP e
    (fun l => (by norm_num : (0:ℝ)<1/10).trans (he l).1) χ G zero_le_one hG Φ hΦ.continuous hT hγ j hj
  apply (hslot.add hstrip).congr' _ EventuallyEq.rfl
  filter_upwards [] with x
  exact sub_add_sub_cancel _ _ _

end
end ArtinMatthews
