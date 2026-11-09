module

public import ArtinMatthews.SpectralMixedCuspBesselFibre


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact Poincare pairing reindexed by the exact source
moduli `c>0`, `(c,r)=1`, with normalized real modulus `s*sqrt(r)*c`.
The zero sector and the genuine noncuspidal remainder stay explicit. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups BigOperators ContDiff InnerProductSpace

namespace ArtinMatthews

def gamma0MixedSourceModulus (r s : ℕ) [NeZero s]
    (c : {c : ℕ // 0 < c ∧ r.Coprime c}) : Ioi (0 : ℕ) :=
  ⟨s*c.val,Nat.mul_pos (NeZero.pos s) c.property.1⟩

theorem gamma0MixedSourceModulus_injective (r s : ℕ) [NeZero s] :
    Function.Injective (gamma0MixedSourceModulus r s) := by
  intro c d h
  apply Subtype.ext
  exact Nat.eq_of_mul_eq_mul_left (NeZero.pos s) (congrArg Subtype.val h)

theorem gamma0MixedSourceModulus_mem_range (r s : ℕ) [NeZero s] (q : Ioi (0 : ℕ)) :
    q ∈ Set.range (gamma0MixedSourceModulus r s) ↔
      ∃ c : ℕ, 0 < c ∧ q.val = s*c ∧ r.Coprime c := by
  constructor
  · rintro ⟨c,rfl⟩
    exact ⟨c.val,c.property.1,rfl,c.property.2⟩
  · rintro ⟨c,hc,hq,hrc⟩
    exact ⟨⟨c,hc,hrc⟩,Subtype.ext hq.symm⟩

theorem gamma0MixedSourceModulus_finsum_reindex (r s : ℕ) [NeZero s]
    (F : Ioi (0 : ℕ) → ℂ)
    (hzero : ∀ q, (¬ ∃ c : ℕ, 0 < c ∧ q.val = s*c ∧ r.Coprime c) → F q = 0) :
    (∑ᶠ q : Ioi (0 : ℕ), F q) =
      ∑ᶠ c : {c : ℕ // 0 < c ∧ r.Coprime c}, F (gamma0MixedSourceModulus r s c) := by
  classical
  let e := gamma0MixedSourceModulus r s
  have hi : (Set.range e).indicator F = F := by
    funext q
    by_cases hq : q ∈ Set.range e
    · exact Set.indicator_of_mem hq _
    · rw [Set.indicator_of_notMem hq, hzero q (mt (gamma0MixedSourceModulus_mem_range r s q).mpr hq)]
  calc
    _ = ∑ᶠ q ∈ Set.range e, F q := by rw [finsum_mem_def,hi]
    _ = ∑ᶠ q : Set.range e, F q.val := (finsum_subtype_eq_finsum_cond _).symm
    _ = _ := (finsum_comp_equiv (f := fun q : Set.range e => F q.val)
      (Equiv.ofInjective e (gamma0MixedSourceModulus_injective r s))).symm

def gamma0MixedBesselSourceFibre (r s : ℕ) [NeZero r] [NeZero s] {a b : ℤ}
    (hab : (r : ℤ)*a-(s : ℤ)*b = 1) (m n : ℤ) (ρ η : ℝ → ℝ)
    (c : {c : ℕ // 0 < c ∧ r.Coprime c}) : ℂ :=
  letI : NeZero c.val := ⟨c.property.1.ne'⟩
  ((r*s*s : ℕ) : ℂ)*(lowerTriMixedResidueSum (NeZero.pos r) hab c.val m n*
    gamma0TrueWidthBesselOrbital (r*s) (gamma0CuspOneOver s) 1 (s*c.val) n m ρ η)

theorem gamma0MixedBesselSourceFibre_eq_native (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (m n : ℤ) (ρ η : ℝ → ℝ) (c : {c : ℕ // 0 < c ∧ r.Coprime c}) :
    gamma0MixedBesselSourceFibre r s hab m n ρ η c =
      gamma0TrueWidthPositiveBesselFibre (r*s) (gamma0CuspOneOver s) 1
        (gamma0MixedSourceModulus r s c) n m ρ η := by
  let _ : NeZero c.val := ⟨c.property.1.ne'⟩
  exact (gamma0MixedBesselGeometricFibre_source r s c.val hcop hab m n ρ η).symm

theorem gamma0PositiveGeometricSum_mixed_source_bessel (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ)) :
    let nN := (gamma0CuspFrequencyStep (r*s) (gamma0CuspOneOver s) : ℤ)*n
    let mN := (gamma0CuspFrequencyStep (r*s) 1 : ℤ)*m
    let ψ := cuspFourierTestSeed ((r*s : ℕ) : ℝ) (Nat.cast_pos.mpr (NeZero.pos (r*s))) nN ρ hρ hcρ hpρ
    let φ := cuspFourierTestSeed ((r*s : ℕ) : ℝ) (Nat.cast_pos.mpr (NeZero.pos (r*s))) mN η hη hcη hpη
    Function.HasFiniteSupport (gamma0MixedBesselSourceFibre r s hab m n ρ η) ∧
      gamma0PositiveGeometricSum (r*s) (gamma0CuspOneOver s) 1 ψ φ =
        ∑ᶠ c : {c : ℕ // 0 < c ∧ r.Coprime c}, gamma0MixedBesselSourceFibre r s hab m n ρ η c := by
  dsimp only
  let F (q : Ioi (0 : ℕ)) :=
    gamma0TrueWidthPositiveBesselFibre (r*s) (gamma0CuspOneOver s) 1 q n m ρ η
  have hP := gamma0PositiveGeometricSum_trueWidth_bessel (r*s) (gamma0CuspOneOver s) 1
    n m hn hm ρ η hρ hη hcρ hcη hpρ hpη
  have hEq : gamma0MixedBesselSourceFibre r s hab m n ρ η = fun c => F (gamma0MixedSourceModulus r s c) :=
    funext (gamma0MixedBesselSourceFibre_eq_native r s hcop hab m n ρ η)
  have hzero (q : Ioi (0 : ℕ)) (hq : ¬ ∃ c : ℕ, 0 < c ∧ q.val = s*c ∧ r.Coprime c) : F q = 0 := by
    let _ : NeZero q.val := ⟨(show 0 < q.val from q.property).ne'⟩
    exact gamma0MixedBesselGeometricFibre_zero_off_source_moduli r s q.val hcop hab m n ρ η hq
  rw [hEq,hP.2]
  exact ⟨Function.HasFiniteSupport.fun_comp_of_injective (gamma0MixedSourceModulus_injective r s) hP.1,
    gamma0MixedSourceModulus_finsum_reindex r s F hzero⟩

theorem gamma0FourierPoincareTest_mixed_source_bessel_pairing (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) :
    let nN := (gamma0CuspFrequencyStep (r*s) (gamma0CuspOneOver s) : ℤ)*n
    let mN := (gamma0CuspFrequencyStep (r*s) 1 : ℤ)*m
    let ψ := cuspFourierTestSeed ((r*s : ℕ) : ℝ) (Nat.cast_pos.mpr (NeZero.pos (r*s))) nN ρ hρ hcρ hpρ
    let φ := cuspFourierTestSeed ((r*s : ℕ) : ℝ) (Nat.cast_pos.mpr (NeZero.pos (r*s))) mN η hη hcη hpη
    let P := gamma0FourierPoincareTest (r*s) (gamma0CuspOneOver s) nN ρ hρ hcρ hpρ
    let Q := gamma0FourierPoincareTest (r*s) 1 mN η hη hcη hpη
    2*gamma0ZeroGeometricSum (r*s) (gamma0CuspOneOver s) 1 ψ φ +
      4*(∑ᶠ c : {c : ℕ // 0 < c ∧ r.Coprime c}, gamma0MixedBesselSourceFibre r s hab m n ρ η c) =
      (∑' i : Gamma0AllHeightSpectralIndex (r*s),
        gamma0FourierPoincareSpectralCoefficient (r*s) i (gamma0CuspOneOver s) Y hY nN
          (gamma0CuspFrequencyStep_mul_ne_zero (r*s) (gamma0CuspOneOver s) hn) ρ*
          star (gamma0FourierPoincareSpectralCoefficient (r*s) i 1 Y hY mN
            (gamma0CuspFrequencyStep_mul_ne_zero (r*s) 1 hm) η)) +
        inner ℂ (gamma0NoncuspidalRemainder (r*s) P) (gamma0NoncuspidalRemainder (r*s) Q) := by
  dsimp only
  rw [← (gamma0PositiveGeometricSum_mixed_source_bessel r s hcop hab
    m n hm hn ρ η hρ hη hcρ hcη hpρ hpη).2]
  exact gamma0FourierPoincareTest_orbital_spectral (r*s) (gamma0CuspOneOver s) 1 Y hY _ _
    (gamma0CuspFrequencyStep_mul_ne_zero (r*s) (gamma0CuspOneOver s) hn)
    (gamma0CuspFrequencyStep_mul_ne_zero (r*s) 1 hm)
    ρ η hρ hη hcρ hcη hpρ hpη hsρ hsη

end ArtinMatthews
