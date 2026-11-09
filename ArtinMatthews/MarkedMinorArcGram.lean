module

public import OAI.NumberTheory.EgyptianFractions.VaughanBilinear
public import OAI.NumberTheory.EgyptianFractions.RationalPhaseSpacing
public import OAI.NumberTheory.EgyptianFractions.RealPhaseEnvelope


set_option backward.privateInPublic true
@[expose] public section

/-!
# The actual bilinear exponential Gram kernel

This module uses the proved rational-spacing and geometric-sum estimates to
bound the actual finite exponential matrix in PD (mem:bilinear-gram). Both
integer interval origins and all complex coefficient squared masses remain
explicit. Resonant frequencies retain their full peak.
-/
namespace ArtinMatthews
open scoped BigOperators ComplexConjugate

private noncomputable abbrev RP := OAI.Problem337.RealPhase.phase

private theorem marked_minor_phase_conj (x : ℝ) : conj (RP x) = RP (-x) := by
  unfold RP OAI.Problem337.RealPhase.phase
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul,map_ofNat,Complex.conj_ofReal,Complex.conj_I]
  ring

private theorem marked_minor_phase_mul_conj (x y : ℝ) :
    RP x * conj (RP y) = RP (x-y) := by
  rw [marked_minor_phase_conj,← OAI.Problem337.RealPhase.phase_add]
  congr 1


/-- The real geometric envelope is dominated by the proved total
nearest-integer reciprocal kernel, including its value at distance zero. -/
theorem marked_minor_envelope_le (M : ℕ) (x : ℝ) :
    OAI.Problem337.RealPhase.envelope M x ≤
      OAI.Problem337.RationalPhaseSpacing.truncatedInv (M : ℝ)
        (OAI.Problem337.RationalPhaseSpacing.intDistance x) := by
  have hd : OAI.Problem337.RealPhase.integerDistance x =
      OAI.Problem337.RationalPhaseSpacing.intDistance x :=
    (OAI.Problem337.RationalPhaseSpacing.intDistance_eq_abs_sub_round x).symm
  rw [OAI.Problem337.RealPhase.envelope,hd,
    OAI.Problem337.RationalPhaseSpacing.truncatedInv]
  split_ifs with hx
  · rfl
  · apply min_le_min_left
    have hp : 0 < OAI.Problem337.RationalPhaseSpacing.intDistance x :=
      lt_of_le_of_ne (OAI.Problem337.RationalPhaseSpacing.intDistance_nonneg x) (Ne.symm hx)
    exact one_div_le_one_div_of_le hp (by linarith)

/-- The actual complex Gram entry at arbitrary integer row origin has the
standard geometric majorant in the difference of the column indices. -/
theorem marked_minor_correlation_le (L : ℤ) (M : ℕ) (θ : ℝ) (n k : ℤ) :
    ‖∑ h ∈ Finset.Ico L (L+(M : ℤ)),
        RP (θ*(h : ℝ)*n) * conj (RP (θ*(h : ℝ)*k))‖ ≤
      OAI.Problem337.RationalPhaseSpacing.truncatedInv (M : ℝ)
        (OAI.Problem337.RationalPhaseSpacing.intDistance (θ*((n : ℝ)-k))) := by
  simp_rw [marked_minor_phase_mul_conj]
  rw [Int.Ico_eq_finset_map,Finset.sum_map]
  simp only [add_sub_cancel_left,Int.toNat_natCast,Function.Embedding.trans_apply,
    Nat.castEmbedding_apply,addLeftEmbedding_apply,Int.cast_add,Int.cast_natCast]
  have he : (∑ j ∈ Finset.range M,
      RP (θ*((L : ℝ)+(j : ℝ))*n-θ*((L : ℝ)+(j : ℝ))*k)) =
      ∑ j ∈ Finset.range M, RP ((θ*((n : ℝ)-k))*((L : ℝ)+j)+0) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring
  rw [he]
  exact (OAI.Problem337.RealPhase.norm_sum_shift_phase_le_envelope
    (θ*((n : ℝ)-k)) 0 L M).trans (marked_minor_envelope_le M _)

/-- Explicit row budget for the actual bilinear Gram matrix. -/
noncomputable def markedMinorGramBudget (M N q : ℕ) : ℝ :=
  (2*((2*N+1 : ℕ) : ℝ)/(q : ℝ)+1) *
    (2*(M : ℝ)+4*(q : ℝ)*(1+Real.log (2*(q : ℝ))))


/-- The actual Gram row bound of PD (mem:bilinear-gram), with arbitrary
integer origins and an explicit absolute constant. -/
theorem marked_minor_gram_row_le (L T : ℤ) (M N : ℕ)
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ-(a : ℝ)/q| ≤ 1/(q : ℝ)^2)
    (n : ℤ) (hn : n ∈ Finset.Ico T (T+(N : ℤ))) :
    (∑ k ∈ Finset.Ico T (T+(N : ℤ)),
      ‖∑ h ∈ Finset.Ico L (L+(M : ℤ)),
        RP (θ*(h : ℝ)*n) * conj (RP (θ*(h : ℝ)*k))‖) ≤
      markedMinorGramBudget M N q := by
  classical
  let J := Finset.Ico T (T+(N : ℤ))
  let D := J.image (fun k => n-k)
  let f := fun h : ℤ => OAI.Problem337.RationalPhaseSpacing.truncatedInv (M : ℝ)
    (OAI.Problem337.RationalPhaseSpacing.intDistance (θ*(h : ℝ)))
  have hf : ∀ h : ℤ, 0 ≤ f h := fun h =>
    OAI.Problem337.RationalPhaseSpacing.truncatedInv_nonneg (Nat.cast_nonneg M)
      (OAI.Problem337.RationalPhaseSpacing.intDistance_nonneg _)
  have hD : D ⊆ Finset.Ico (-(N : ℤ)) (-(N : ℤ)+(2*N+1 : ℕ)) := by
    intro h hh
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hh
    have hk' := Finset.mem_Ico.mp hk
    have hn' := Finset.mem_Ico.mp hn
    apply Finset.mem_Ico.mpr
    push_cast
    omega
  calc
    _ ≤ ∑ k ∈ J, f (n-k) := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [f,Int.cast_sub] using marked_minor_correlation_le L M θ n k
    _ = ∑ h ∈ D, f h := by
      rw [Finset.sum_image]
      intro i _ j _ he
      change n-i = n-j at he
      omega
    _ ≤ ∑ h ∈ Finset.Ico (-(N : ℤ)) (-(N : ℤ)+(2*N+1 : ℕ)), f h :=
      Finset.sum_le_sum_of_subset_of_nonneg hD (fun h _ _ => hf h)
    _ ≤ _ := OAI.Problem337.RationalPhaseSpacing.sum_truncatedInv_intDistance_interval_le
      θ a q hq hcop happrox (-(N : ℤ)) (2*N+1) M (Nat.cast_nonneg M)

/-- The actual bilinear exponential operator has the proved Gram budget as
its squared L² bound; all complex coefficient masses are retained. -/
theorem marked_minor_bilinear_energy_le (L T : ℤ) (M N : ℕ)
    (θ : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q) (hcop : IsCoprime a (q : ℤ))
    (happrox : |θ-(a : ℝ)/q| ≤ 1/(q : ℝ)^2) (b : ℤ → ℂ) :
    (∑ h ∈ Finset.Ico L (L+(M : ℤ)),
      ‖∑ n ∈ Finset.Ico T (T+(N : ℤ)), b n * RP (θ*(h : ℝ)*n)‖^2) ≤
      markedMinorGramBudget M N q *
        (∑ n ∈ Finset.Ico T (T+(N : ℤ)), ‖b n‖^2) := by
  let I := Finset.Ico L (L+(M : ℤ))
  let J := Finset.Ico T (T+(N : ℤ))
  let z := fun h n : ℤ => RP (θ*(h : ℝ)*n)
  have hbase := OAI.Problem337.VaughanBilinear.energy_le_correlations I J b z
  have hschur := OAI.Problem337.VaughanBilinear.symmetric_weighted_sum_le J
    (fun n => ‖b n‖)
    (fun n k => ‖∑ h ∈ I, z h n * (starRingEnd ℂ) (z h k)‖)
    (fun _ _ _ _ => norm_nonneg _)
    (fun n _ k _ => OAI.Problem337.VaughanBilinear.correlation_norm_symm I z n k)
  refine hbase.trans (hschur.trans ?_)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hrow := marked_minor_gram_row_le L T M N θ a q hq hcop happrox n hn
  simpa only [I,J,z,mul_comm] using mul_le_mul_of_nonneg_left hrow (sq_nonneg ‖b n‖)


/-- The exact Gram budget is nonnegative for every positive rational denominator. -/
theorem markedMinorGramBudget_nonneg (M N q : ℕ) (hq : 0 < q) :
    0 ≤ markedMinorGramBudget M N q := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlog : 0 ≤ Real.log (2*(q : ℝ)) := Real.log_nonneg (by linarith)
  unfold markedMinorGramBudget
  positivity

end ArtinMatthews
