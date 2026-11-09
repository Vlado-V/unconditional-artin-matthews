module

public import ArtinMatthews.SourceJHolomorphicTrace


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite source coefficients pass through the complete
holomorphic weight series and the complete signed modulus series. -/
namespace ArtinMatthews
open Set
open scoped MatrixGroups BigOperators
noncomputable section

private theorem finite_norm_sum_summable {ι κ : Type*} (v : Finset ι) (F : ι → κ → ℂ)
    (hs : ∀ i ∈ v, Summable (fun j => ‖F i j‖)) :
    Summable (fun j => ‖∑ i ∈ v, F i j‖) := by
  classical
  have hmajor : Summable (fun j => ∑ i ∈ v, ‖F i j‖) := by
    induction v using Finset.induction_on with
    | empty => simp
    | @insert i v hi ih =>
      have ha := hs i (Finset.mem_insert_self _ _)
      have hb := ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))
      simpa only [Finset.sum_insert hi] using ha.add hb
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun j => norm_sum_le v (fun i => F i j)) hmajor

def sourceJHolomorphicMixedPacketTerm {ι : Type*} (f : ℝ → ℂ)
    (r s : ℕ) [NeZero r] [NeZero s]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (negative : Bool)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) (n : ℕ+) (j : ℕ) : ℂ :=
  spectralJHolomorphicCoefficient f (2*j+2)*
    ∑ i ∈ v, α i*gamma0PeterssonInner (r*s) (2*j+2)
      (spectralPeterssonSignVector negative (gamma0PeterssonSourceAtkin r s hab (2*j+2) n))
      (spectralPeterssonSignVector negative (gamma0PeterssonSourceInfinity (r*s) (2*j+2) (m i)))

def sourceJHolomorphicMixedPacketSeries {ι : Type*} (f : ℝ → ℂ)
    (r s : ℕ) [NeZero r] [NeZero s]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (negative : Bool)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) (n : ℕ+) : ℂ :=
  ∑' j : ℕ, sourceJHolomorphicMixedPacketTerm f r s hab negative v α m n j

theorem sourceJHolomorphicMixedPacketTerm_eq_sum {ι : Type*} (f : ℝ → ℂ)
    (r s : ℕ) [NeZero r] [NeZero s]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (negative : Bool)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) (n : ℕ+) (j : ℕ) :
    sourceJHolomorphicMixedPacketTerm f r s hab negative v α m n j =
      ∑ i ∈ v, α i*sourceJHolomorphicMixedGramTerm f r s hab negative (m i) n j := by
  unfold sourceJHolomorphicMixedPacketTerm sourceJHolomorphicMixedGramTerm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sourceJHolomorphicMixedPacketTerm_summable {ι : Type*} (f : ℝ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hr : 1 < r) (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (negative : Bool)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) (n : ℕ+) :
    Summable (fun j : ℕ => ‖sourceJHolomorphicMixedPacketTerm f r s hab negative v α m n j‖) := by
  have hs := finite_norm_sum_summable v
    (fun i j => α i*sourceJHolomorphicMixedGramTerm f r s hab negative (m i) n j) (by
      intro i _
      simpa only [norm_mul] using
        (sourceJHolomorphicMixedGramTerm_summable f hf hc hp r s hr hcop hab negative (m i) n).mul_left ‖α i‖)
  exact hs.congr fun j => congrArg norm (sourceJHolomorphicMixedPacketTerm_eq_sum f r s hab negative v α m n j).symm

theorem sourceJHolomorphicMixedPacketSeries_linear {ι : Type*} (f : ℝ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hr : 1 < r) (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (negative : Bool)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) (n : ℕ+) :
    (∑ i ∈ v, α i*sourceJHolomorphicMixedGramSeries f r s hab negative (m i) n) =
      sourceJHolomorphicMixedPacketSeries f r s hab negative v α m n := by
  have hs (i : ι) (_ : i ∈ v) :
      Summable (fun j => α i*sourceJHolomorphicMixedGramTerm f r s hab negative (m i) n j) :=
    (sourceJHolomorphicMixedGramTerm_summable f hf hc hp r s hr hcop hab negative (m i) n).of_norm.mul_left _
  calc
    _ = ∑ i ∈ v, ∑' j : ℕ, α i*sourceJHolomorphicMixedGramTerm f r s hab negative (m i) n j := by
      simp only [sourceJHolomorphicMixedGramSeries,tsum_mul_left]
    _ = ∑' j : ℕ, ∑ i ∈ v, α i*sourceJHolomorphicMixedGramTerm f r s hab negative (m i) n j :=
      (Summable.tsum_finsetSum hs).symm
    _ = _ := tsum_congr fun j => (sourceJHolomorphicMixedPacketTerm_eq_sum f r s hab negative v α m n j).symm

theorem sourceJHolomorphicMixedPacketSeries_eq_odd {ι : Type*} (f : ℝ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hr : 1 < r) (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (negative : Bool)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) (n : ℕ+) :
    sourceJHolomorphicMixedPacketSeries f r s hab negative v α m n =
      ∑' c : Ioi (0 : ℕ), ∑ i ∈ v, α i*
        gamma0ABLOppositeGeometricTerm (r*s) (gamma0CuspOneOver s) 1 c
          (sourceJHolomorphicSignedIndex negative n) (sourceJHolomorphicSignedIndex negative (m i))
          (spectralJOddSynthesis f) := by
  rw [← sourceJHolomorphicMixedPacketSeries_linear f hf hc hp r s hr hcop hab negative v α m n]
  simp_rw [sourceJHolomorphicMixedGramSeries_eq_odd f hf hc hp r s hr hcop hab negative]
  have hs (i : ι) (_ : i ∈ v) : Summable (fun c : Ioi (0 : ℕ) => α i*
      gamma0ABLOppositeGeometricTerm (r*s) (gamma0CuspOneOver s) 1 c
        (sourceJHolomorphicSignedIndex negative n) (sourceJHolomorphicSignedIndex negative (m i))
        (spectralJOddSynthesis f)) :=
    (sourceJHolomorphicOdd_geometric_summable f hf hc hp (r*s) (gamma0CuspOneOver s) negative (m i) n).of_norm.mul_left _
  simpa only [tsum_mul_left] using (Summable.tsum_finsetSum hs).symm

theorem sourceJHolomorphicMixedPacketOdd_summable {ι : Type*} (f : ℝ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (N : ℕ) [NeZero N] (b : SL(2, ℤ)) (negative : Bool)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) (n : ℕ+) :
    Summable (fun c : Ioi (0 : ℕ) => ‖∑ i ∈ v, α i*
      gamma0ABLOppositeGeometricTerm N b 1 c
        (sourceJHolomorphicSignedIndex negative n) (sourceJHolomorphicSignedIndex negative (m i))
        (spectralJOddSynthesis f)‖) := by
  apply finite_norm_sum_summable
  intro i _
  simpa only [norm_mul] using
    (sourceJHolomorphicOdd_geometric_summable f hf hc hp N b negative (m i) n).mul_left ‖α i‖

end
end ArtinMatthews
