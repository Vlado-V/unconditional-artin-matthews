module

public import ArtinMatthews.SourceJHolomorphicPacket
public import ArtinMatthews.SpectralPeterssonSourceHilbert


set_option backward.privateInPublic true
@[expose] public section

/-! The all-even source trace and its finite packet are literal inner
products of the checked signed source vectors in the native Petersson L² space. -/
namespace ArtinMatthews
open Set
open scoped MatrixGroups BigOperators InnerProductSpace
noncomputable section

private theorem sourceJ_weight_even (j : ℕ) : Even (2*j+2) := ⟨j+1,by omega⟩

private theorem sourceJ_weight_lower (j : ℕ) : 2 ≤ 2*j+2 := by omega

def sourceJHolomorphicInfinityPacketL2 {ι : Type*} (N k : ℕ) [NeZero N]
    (hk : 2 ≤ k) (hEven : Even k) (negative : Bool)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) : Gamma0PeterssonL2 N :=
  ∑ i ∈ v, α i • gamma0PeterssonSourceInfinityL2 N k hk hEven negative (m i)

theorem sourceJHolomorphicMixedGramSeries_eq_hilbert (f : ℝ → ℂ)
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (negative : Bool) (m n : ℕ+) :
    sourceJHolomorphicMixedGramSeries f r s hab negative m n =
      ∑' j : ℕ, spectralJHolomorphicCoefficient f (2*j+2)*
        ⟪gamma0PeterssonSourceAtkinL2 r s hcop hab (2*j+2) (sourceJ_weight_lower j) (sourceJ_weight_even j) negative n,
          gamma0PeterssonSourceInfinityL2 (r*s) (2*j+2) (sourceJ_weight_lower j) (sourceJ_weight_even j) negative m⟫_ℂ := by
  apply tsum_congr
  intro j
  rw [gamma0PeterssonSourceL2_mixed_inner]
  rfl

theorem sourceJHolomorphicMixedPacketTerm_eq_inner {ι : Type*} (f : ℝ → ℂ)
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (negative : Bool)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) (n : ℕ+) (j : ℕ) :
    sourceJHolomorphicMixedPacketTerm f r s hab negative v α m n j =
      spectralJHolomorphicCoefficient f (2*j+2)*
        ⟪gamma0PeterssonSourceAtkinL2 r s hcop hab (2*j+2) (sourceJ_weight_lower j) (sourceJ_weight_even j) negative n,
          sourceJHolomorphicInfinityPacketL2 (r*s) (2*j+2) (sourceJ_weight_lower j) (sourceJ_weight_even j) negative v α m⟫_ℂ := by
  unfold sourceJHolomorphicInfinityPacketL2
  rw [inner_sum]
  simp_rw [inner_smul_right,gamma0PeterssonSourceL2_mixed_inner]
  rfl

theorem sourceJHolomorphicMixedPacketSeries_eq_hilbert {ι : Type*} (f : ℝ → ℂ)
    (r s : ℕ) [NeZero r] [NeZero s] (hcop : r.Coprime s)
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (negative : Bool)
    (v : Finset ι) (α : ι → ℂ) (m : ι → ℕ+) (n : ℕ+) :
    sourceJHolomorphicMixedPacketSeries f r s hab negative v α m n =
      ∑' j : ℕ, spectralJHolomorphicCoefficient f (2*j+2)*
        ⟪gamma0PeterssonSourceAtkinL2 r s hcop hab (2*j+2) (sourceJ_weight_lower j) (sourceJ_weight_even j) negative n,
          sourceJHolomorphicInfinityPacketL2 (r*s) (2*j+2) (sourceJ_weight_lower j) (sourceJ_weight_even j) negative v α m⟫_ℂ := by
  apply tsum_congr
  intro j
  exact sourceJHolomorphicMixedPacketTerm_eq_inner f r s hcop hab negative v α m n j

end
end ArtinMatthews
