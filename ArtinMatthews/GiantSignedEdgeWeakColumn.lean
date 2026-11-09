module

public import ArtinMatthews.GiantSignedEdgeColumnApply


set_option backward.privateInPublic true
@[expose] public section

/-! The original weighted edge column follows from the literal factorial
reversal, full-memory Fubini and the transposed positive row estimate. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
variable [∀ j, ∀ p : P j, NeZero p.val] {t : J → ℕ}

omit [DecidableEq J] in
theorem giantSignedEdgeWeightedTest_summable (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) {B u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (hfn : ∀ target out, 0 ≤ f target out)
    (hf : ∀ target out, f target out ≤ B * u ^ (∑ j, out.1 j))
    (source : GiantSignedPrimeTuple P t) :
    Summable (fun m : GiantSignedMemory P =>
      giantSignedMemoryMass ν m * v ^ (∑ j, m.1 j) * f source m) := by
  have hs := (giantSignedMemory_exponential_summable ν hν (v * u)
    (mul_nonneg hv hu)).mul_left B
  apply hs.of_nonneg_of_le
  · intro m
    exact mul_nonneg (mul_nonneg (giantSignedMemoryMass_nonneg ν hν m)
      (pow_nonneg hv _)) (hfn source m)
  · intro m
    calc
      _ ≤ giantSignedMemoryMass ν m * v ^ (∑ j, m.1 j) *
          (B * u ^ (∑ j, m.1 j)) := mul_le_mul_of_nonneg_left (hf source m)
        (mul_nonneg (giantSignedMemoryMass_nonneg ν hν m) (pow_nonneg hv _))
      _ = _ := by rw [mul_pow]; ring

theorem giantSignedEdgeApply_weak_column_bound (ν : (j : J) → P j → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (V : J → ℝ) {vmin vmax massMax ρ v B u : ℝ}
    (hvmin : 0 < vmin) (hVmin : ∀ j, vmin ≤ V j) (hVmax : ∀ j, V j ≤ vmax)
    (hMass : ∀ j, (∑ p : P j, ν j p) ≤ massMax)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hv : 1 ≤ v) (hB : 0 ≤ B) (hu : 1 ≤ u)
    (tmax : ℕ) (ht : ∀ j, t j ≤ tmax) (d : ℤ) (D : ℕ)
    (f : GiantSignedPrimeTuple P t → GiantSignedMemory P → ℝ)
    (hfn : ∀ target out, 0 ≤ f target out)
    (hf : ∀ target out, f target out ≤ B * u ^ (∑ j, out.1 j))
    (hsym : ∀ target m σ, f target (giantSignedMemoryPermute m σ) = f target m) :
    (∑ source : GiantSignedPrimeTuple P t, giantSignedFreePrimeRealMass ν source *
      ∑' m : GiantSignedMemory P, giantSignedMemoryMass ν m * v ^ (∑ j, m.1 j) *
        ‖giantSignedEdgeApply (fun j p => (ν j p : ℂ)) V ρ d D source
          (fun target out => (f target out : ℂ)) m‖) ≤
      (giantSignedEdgeReverseConstant vmin vmax tmax *
        giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax tmax) ^ Fintype.card J *
      ∑ source : GiantSignedPrimeTuple P t, giantSignedFreePrimeRealMass ν source *
        ∑' m : GiantSignedMemory P,
          giantSignedMemoryMass ν m * v ^ (∑ j, m.1 j) * f source m := by
  classical
  let F : GiantSignedEdgeCoupledTest P t ℝ := giantSignedEdgeColumnTest D v f
  let G : GiantSignedEdgeCoupledTest P t ℝ := giantSignedEdgeReverseColumnTest V D v f
  let R := (giantSignedEdgeReverseConstant vmin vmax tmax) ^ Fintype.card J
  let C := (giantSignedEdgeReverseConstant vmin vmax tmax *
    giantSignedEdgeUniformConstant ρ v vmin⁻¹ massMax tmax) ^ Fintype.card J
  have hv0 : 0 ≤ v := le_trans zero_le_one hv
  have hu0 : 0 ≤ u := le_trans zero_le_one hu
  have hVp (j : J) : 0 < V j := lt_of_lt_of_le hvmin (hVmin j)
  have hR : 0 ≤ R := pow_nonneg (giantSignedEdgeReverseConstant_nonneg _ _ _) _
  have hF0 : ∀ S T source target old out, 0 ≤ F S T source target old out :=
    giantSignedEdgeColumnTest_nonneg D hv0 f hfn
  have hG0 : ∀ S T source target old out, 0 ≤ G S T source target old out :=
    giantSignedEdgeReverseColumnTest_nonneg V (fun j => (hVp j).le) D hv0 f hfn
  have hFg : ∀ S T source target old out,
      F S T source target old out ≤ B * v ^ (∑ j, old.1 j) * u ^ (∑ j, out.1 j) :=
    giantSignedEdgeColumnTest_growth D hv0 hu0 hB f hf
  have hGg : ∀ S T source target old out,
      G S T source target old out ≤ (B * R) * u ^ (∑ j, old.1 j) * v ^ (∑ j, out.1 j) :=
    giantSignedEdgeReverseColumnTest_growth V hvmin hVmin hVmax D hv0 hu0 hB
      tmax ht f hf
  have hFblocks := giantSignedEdgeCoupledPairing_blocks ν hν V hVp hρ hρ1 d F hF0
    B v u hB hv hu hFg
  have hGblocks := giantSignedEdgeCoupledPairing_blocks ν hν V hVp hρ hρ1 (-d) G hG0
    (B * R) u v (mul_nonneg hB hR) hu hv hGg
  have heq : giantSignedEdgeCoupledPairing ν V ρ d F =
      giantSignedEdgeCoupledPairing ν V ρ (-d) G := by
    calc
      _ = ∑ S : (j : J) → Finset (Fin (t j)), ∑ T : (j : J) → Finset (Fin (t j)),
          ∑' n : J → ℕ, giantSignedEdgeRealStorePairing ν V ρ d n S T (F S T) := hFblocks
      _ = ∑ S : (j : J) → Finset (Fin (t j)), ∑ T : (j : J) → Finset (Fin (t j)),
          ∑' n : J → ℕ, giantSignedEdgeRealStorePairing ν V ρ (-d) n T S (G T S) := by
        apply Finset.sum_congr rfl
        intro S _
        apply Finset.sum_congr rfl
        intro T _
        exact tsum_congr (fun n => giantSignedEdgeColumnTest_block_reverse ν V
          (fun j => ne_of_gt (hVp j)) ρ d D v f hsym n S T)
      _ = ∑ S : (j : J) → Finset (Fin (t j)), ∑ T : (j : J) → Finset (Fin (t j)),
          ∑' n : J → ℕ, giantSignedEdgeRealStorePairing ν V ρ (-d) n S T (G S T) :=
        Finset.sum_comm
      _ = _ := hGblocks.symm
  have hkernel (source : GiantSignedPrimeTuple P t) (m : GiantSignedMemory P) :
      giantSignedEdgeTransposePositiveApply ν V ρ (-d) D source
        (fun _ out => v ^ (∑ j, out.1 j)) m ≤ v ^ (∑ j, m.1 j) * C := by
    simpa only [one_mul] using giantSignedEdgeTransposePositiveApply_bound ν hν V
      hvmin hVmin hVmax hMass hρ hρ1 hv zero_le_one tmax ht (-d) D source
      (fun _ out => v ^ (∑ j, out.1 j))
      (fun _ out => pow_nonneg hv0 _) (fun _ _ => by simp) m
  have hbound : giantSignedEdgeCoupledPairing ν V ρ (-d) G ≤
      C * ∑ source : GiantSignedPrimeTuple P t, giantSignedFreePrimeRealMass ν source *
        ∑' m : GiantSignedMemory P,
          giantSignedMemoryMass ν m * v ^ (∑ j, m.1 j) * f source m := by
    unfold giantSignedEdgeCoupledPairing
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro source _
    have hsL := giantSignedEdgeCoupled_memory_summable ν hν V hVp hρ hρ1 (-d) G hG0
      (B * R) u v (mul_nonneg hB hR) hu hv hGg source
    have hsR := (giantSignedEdgeWeightedTest_summable ν hν hu0 hv0 f hfn hf source).mul_left C
    have hlocal (m : GiantSignedMemory P) :
        giantSignedMemoryMass ν m * giantSignedEdgeCoupledApply ν V ρ (-d) G source m ≤
          C * (giantSignedMemoryMass ν m * v ^ (∑ j, m.1 j) * f source m) := by
      change giantSignedMemoryMass ν m *
        giantSignedEdgeCoupledApply ν V ρ (-d) (giantSignedEdgeReverseColumnTest V D v f)
          source m ≤ _
      rw [giantSignedEdgeReverseColumnTest_apply]
      calc
        _ ≤ giantSignedMemoryMass ν m * (f source m * (v ^ (∑ j, m.1 j) * C)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hkernel source m) (hfn source m))
            (giantSignedMemoryMass_nonneg ν hν m)
        _ = _ := by ring
    have hsum := hsL.tsum_le_tsum hlocal hsR
    rw [tsum_mul_left] at hsum
    calc
      _ ≤ giantSignedFreePrimeRealMass ν source *
          (C * ∑' m : GiantSignedMemory P,
            giantSignedMemoryMass ν m * v ^ (∑ j, m.1 j) * f source m) :=
        mul_le_mul_of_nonneg_left hsum (giantSignedFreePrimeRealMass_nonneg ν hν source)
      _ = _ := by ring
  calc
    _ = giantSignedEdgeCoupledPairing ν V ρ d F := by
      unfold giantSignedEdgeCoupledPairing
      apply Finset.sum_congr rfl
      intro source _
      congr 1
      apply tsum_congr
      intro m
      change giantSignedMemoryMass ν m * v ^ (∑ j, m.1 j) * _ =
        giantSignedMemoryMass ν m *
          giantSignedEdgeCoupledApply ν V ρ d (giantSignedEdgeColumnTest D v f) source m
      rw [giantSignedEdgeApply_ofReal_norm ν hν V (fun j => (hVp j).le) hρ d D f hfn,
        giantSignedEdgeColumnTest_apply]
      ring
    _ = giantSignedEdgeCoupledPairing ν V ρ (-d) G := heq
    _ ≤ _ := hbound

end
end ArtinMatthews
