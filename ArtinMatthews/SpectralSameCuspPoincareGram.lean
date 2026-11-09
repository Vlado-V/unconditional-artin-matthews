module

public import ArtinMatthews.SpectralTrueWidthBesselHeightCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite Gram matrix of compact same-cusp Fourier tests.
The diagonal is evaluated by the primitive translation lattice, and
the remaining term is the genuine positive geometric sum. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace BigOperators

namespace ArtinMatthews

theorem gamma0FourierPoincareTest_sameCusp_gram (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    (m n : ℤ) (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ)) :
    let d := gamma0CuspFrequencyStep N r
    let mN := (d : ℤ)*m
    let nN := (d : ℤ)*n
    let ψ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) mN ρ hρ hcρ hpρ
    let φ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) nN η hη hcη hpη
    inner ℂ (gamma0FourierPoincareTest N r mN ρ hρ hcρ hpρ)
      (gamma0FourierPoincareTest N r nN η hη hcη hpη) =
      (if m = n then ((4*(d : ℝ)*(N : ℝ)*cuspFourierHeightPairing ρ η : ℝ) : ℂ) else 0) +
        4*gamma0PositiveGeometricSum N r r ψ φ := by
  dsimp only
  rw [gamma0FourierPoincareTest_sign_sectors N r r _ _ ρ η hρ hη hcρ hcη hpρ hpη,
    gamma0ZeroGeometricSum_sameCusp_fourier N r m n ρ η hρ hη hcρ hcη hpρ hpη]
  by_cases hmn : m = n
  · simp only [hmn,ite_true,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_natCast]
    ring
  · simp only [hmn,ite_false,mul_zero]

theorem gamma0FourierPoincarePacket_sameCusp_gram {ι : Type*} (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (t : Finset ι) (α : ι → ℂ) (ν : ι → ℤ) (hν : Function.Injective ν)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) :
    let d := gamma0CuspFrequencyStep N r
    let nN j := (d : ℤ)*ν j
    let ψ j := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) (nN j) ρ hρ hcρ hpρ
    let P := gamma0FourierPoincarePacket N t α (fun _ => r) nN (fun _ => ρ)
      (fun _ => hρ) (fun _ => hcρ) (fun _ => hpρ)
    ((‖P‖^2 : ℝ) : ℂ) =
      ((4*(d : ℝ)*(N : ℝ)*cuspFourierHeightPairing ρ ρ*(∑ j ∈ t, ‖α j‖^2) : ℝ) : ℂ) +
        4*(∑ j ∈ t, ∑ k ∈ t, star (α j)*α k*gamma0PositiveGeometricSum N r r (ψ j) (ψ k)) := by
  classical
  dsimp only
  let d := gamma0CuspFrequencyStep N r
  let nN j := (d : ℤ)*ν j
  let ψ j := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) (nN j) ρ hρ hcρ hpρ
  let P := gamma0FourierPoincarePacket N t α (fun _ => r) nN (fun _ => ρ)
    (fun _ => hρ) (fun _ => hcρ) (fun _ => hpρ)
  let D : ℝ := 4*(d : ℝ)*(N : ℝ)*cuspFourierHeightPairing ρ ρ
  let A (j k : ι) := star (α j)*α k
  let G (j k : ι) := gamma0PositiveGeometricSum N r r (ψ j) (ψ k)
  have hdiag (j : ι) (hj : j ∈ t) :
      (∑ k ∈ t, A j k*(if ν j = ν k then (D : ℂ) else 0)) = ((D*‖α j‖^2 : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single_of_mem j hj]
    · have hα : star (α j)*α j = ((‖α j‖^2 : ℝ) : ℂ) := by
        change (starRingEnd ℂ) (α j)*α j = _
        rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
      change (star (α j)*α j)*(if ν j = ν j then (D : ℂ) else 0) = _
      rw [ite_eq_left rfl,hα]
      exact (mul_comm _ _).trans (Complex.ofReal_mul D (‖α j‖^2)).symm
    · intro k _ hkj
      have hne : ν j ≠ ν k := fun he => hkj (hν he).symm
      simp only [hne,ite_false,mul_zero]
  change ((‖P‖^2 : ℝ) : ℂ) = ((D*(∑ j ∈ t, ‖α j‖^2) : ℝ) : ℂ) + 4*(∑ j ∈ t, ∑ k ∈ t, A j k*G j k)
  calc
    _ = inner ℂ P P := by
      rw [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]
      rfl
    _ = ∑ j ∈ t, ∑ k ∈ t, A j k*((if ν j = ν k then (D : ℂ) else 0)+4*G j k) := by
      unfold P gamma0FourierPoincarePacket
      rw [sum_inner]
      simp only [inner_sum,inner_smul_left,inner_smul_right]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [gamma0FourierPoincareTest_sameCusp_gram N r (ν j) (ν k) ρ ρ hρ hρ hcρ hcρ hpρ hpρ]
      change α k*(star (α j)*((if ν j = ν k then (D : ℂ) else 0)+4*G j k)) = _
      unfold A
      ring
    _ = (∑ j ∈ t, ∑ k ∈ t, A j k*(if ν j = ν k then (D : ℂ) else 0)) +
          4*(∑ j ∈ t, ∑ k ∈ t, A j k*G j k) := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      congr 1
      calc
        _ = ∑ j ∈ t, ((D*‖α j‖^2 : ℝ) : ℂ) := Finset.sum_congr rfl hdiag
        _ = _ := by rw [← Complex.ofReal_sum,← Finset.mul_sum]

end ArtinMatthews
