module

public import ArtinMatthews.SpectralPeterssonFourierGeometric
public import ArtinMatthews.SpectralPeterssonReproducing
public import ArtinMatthews.SpectralPeterssonWeightedBound


set_option backward.privateInPublic true
@[expose] public section

/-! The actual normalized holomorphic Gram for the absolute convergence
range, with the positive-modulus Bessel terms and exact zero sector. -/

noncomputable section
open Matrix Set MeasureTheory UpperHalfPlane
open scoped MatrixGroups ComplexConjugate

namespace ArtinMatthews

def gamma0PeterssonNormalized (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (n : ℕ+) (z : UpperHalfPlane) : ℂ :=
  (spectralPeterssonNormalization k n : ℂ)*gamma0PeterssonPoincare N a k (n : ℕ) z

def gamma0PeterssonGramModulusTerm (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (m n : ℕ+) (c : Ioi (0 : ℕ)) : ℂ :=
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  let C := gamma0TrueWidthModulus N b a (c.val : ℝ)
  gamma0TrueWidthKloostermanSum N b a c.val (n : ℤ) (m : ℤ)*
    (2*(Real.pi : ℂ)*Complex.I^(-(k : ℤ))/(C : ℂ))*
    Complex.besselJ ((k-1 : ℕ) : ℂ) (spectralPeterssonBesselArgument m n C : ℂ)

theorem gamma0PeterssonInner_scale_real (N k : ℕ) (r s : ℝ) (F G : UpperHalfPlane → ℂ) :
    gamma0PeterssonInner N k (fun z => (r : ℂ)*F z) (fun z => (s : ℂ)*G z) =
      ((r*s : ℝ) : ℂ)*gamma0PeterssonInner N k F G := by
  unfold gamma0PeterssonInner
  rw [← integral_const_mul]
  congr 1
  funext z
  unfold UpperHalfPlane.petersson
  simp only [map_mul,Complex.conj_ofReal,Complex.ofReal_mul]
  ring

theorem gamma0PeterssonInner_poincare (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (hk : 3 ≤ k) (hEven : Even k) (m n : ℕ+) (d : ℂ)
    (h0 : ∀ (y : ℝ) (hy : 0 < y), gamma0PeterssonZeroFourierTerm N b a k m n y hy = d) :
    gamma0PeterssonInner N k (gamma0PeterssonPoincare N b k (n : ℕ))
      (gamma0PeterssonPoincare N a k (m : ℕ)) =
        (spectralPeterssonReproducingMass k n : ℂ)*
          (d+∑' c, gamma0PeterssonPositiveModulusTerm N b a k m n c) := by
  let F := gamma0PeterssonPoincare N a k (m : ℕ)
  have hF (γ : CongruenceSubgroup.Gamma0 N) : spectralHolomorphicSlash k (atkinRealMap γ.val) F = F :=
    gamma0PeterssonPoincare_slash_gamma0 N a γ k (m : ℕ) hk hEven
  have hChart := gamma0PeterssonPoincare_slash_cusp N b a k (m : ℕ) hk hEven
  obtain ⟨M,hM⟩ := gamma0PeterssonPoincareChart_weighted_bound N b a k hk hEven m
  change gamma0PeterssonInner N k (gamma0PeterssonPoincare N b k (n : ℕ)) F = _
  refine gamma0PeterssonInner_reproduce N b k hk hEven n F hF ?_ M ?_ _ ?_
  · rw [hChart]
    exact gamma0PeterssonPoincareChart_continuous N b a k (m : ℕ) hk
  · intro z
    rw [hChart]
    exact hM z
  · intro y hy
    rw [hChart,(gamma0PeterssonFourierAtHeight_geometric N b a k hk m n y hy).2,h0 y hy]

theorem gamma0PeterssonNormalized_gram (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (k : ℕ) (hk : 3 ≤ k) (hEven : Even k) (m n : ℕ+) (d : ℂ)
    (h0 : ∀ (y : ℝ) (hy : 0 < y), gamma0PeterssonZeroFourierTerm N b a k m n y hy = d) :
    Summable (gamma0PeterssonGramModulusTerm N b a k m n) ∧
      gamma0PeterssonInner N k (gamma0PeterssonNormalized N b k n) (gamma0PeterssonNormalized N a k m) =
        ((Real.sqrt (spectralPeterssonReproducingMass k n)/
          Real.sqrt (spectralPeterssonReproducingMass k m) : ℝ) : ℂ)*d +
          ∑' c, gamma0PeterssonGramModulusTerm N b a k m n c := by
  let u := ((Real.sqrt (spectralPeterssonReproducingMass k n)/
    Real.sqrt (spectralPeterssonReproducingMass k m) : ℝ) : ℂ)
  have hu : u*((Real.sqrt ((n : ℝ)/(m : ℝ)) : ℝ) : ℂ)^(k-1) = 1 := by
    have h := congrArg Complex.ofReal (spectralPeterssonNormalization_ratio k (by omega) m n)
    simpa only [u,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_one] using h
  have hterm (c : Ioi (0 : ℕ)) : u*gamma0PeterssonPositiveModulusTerm N b a k m n c =
      gamma0PeterssonGramModulusTerm N b a k m n c := by
    let _ : NeZero c.val := ⟨c.property.ne'⟩
    dsimp only [gamma0PeterssonPositiveModulusTerm,gamma0PeterssonGramModulusTerm]
    linear_combination (gamma0TrueWidthKloostermanSum N b a c.val (n : ℤ) (m : ℤ)*
      (2*(Real.pi : ℂ)*Complex.I^(-(k : ℤ))/(gamma0TrueWidthModulus N b a (c.val : ℝ) : ℂ))*
      Complex.besselJ ((k-1 : ℕ) : ℂ)
        (spectralPeterssonBesselArgument m n (gamma0TrueWidthModulus N b a (c.val : ℝ)) : ℂ))*hu
  have hs := (gamma0PeterssonFourierAtHeight_geometric N b a k hk m n 1 zero_lt_one).1
  refine ⟨(hs.mul_left u).congr hterm,?_⟩
  unfold gamma0PeterssonNormalized
  rw [gamma0PeterssonInner_scale_real,gamma0PeterssonInner_poincare N b a k hk hEven m n d h0,
    ← mul_assoc,← Complex.ofReal_mul,spectralPeterssonNormalization_mass k (by omega)]
  change u*(d+∑' c, gamma0PeterssonPositiveModulusTerm N b a k m n c) = _
  rw [mul_add,← tsum_mul_left]
  congr 1
  exact tsum_congr hterm

theorem gamma0PeterssonNormalized_same_cusp_gram (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (hk : 3 ≤ k) (hEven : Even k) (m n : ℕ+) :
    Summable (gamma0PeterssonGramModulusTerm N a a k m n) ∧
      gamma0PeterssonInner N k (gamma0PeterssonNormalized N a k n) (gamma0PeterssonNormalized N a k m) =
        (if m = n then 1 else 0)+∑' c, gamma0PeterssonGramModulusTerm N a a k m n c := by
  obtain ⟨hs,h⟩ := gamma0PeterssonNormalized_gram N a a k hk hEven m n
    (if m = n then 1 else 0) (gamma0PeterssonZeroFourierTerm_same_chart N a k m n)
  refine ⟨hs,?_⟩
  by_cases he : m = n
  · subst m
    simpa only [if_pos rfl,div_self (ne_of_gt (Real.sqrt_pos.mpr
      (spectralPeterssonReproducingMass_pos k (by omega) n))),Complex.ofReal_one,one_mul] using h
  · simpa only [if_neg he,mul_zero] using h

theorem gamma0PeterssonNormalized_inequivalent_gram (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (h : ¬ gamma0EisensteinCuspsEquivalent N b a)
    (k : ℕ) (hk : 3 ≤ k) (hEven : Even k) (m n : ℕ+) :
    Summable (gamma0PeterssonGramModulusTerm N b a k m n) ∧
      gamma0PeterssonInner N k (gamma0PeterssonNormalized N b k n) (gamma0PeterssonNormalized N a k m) =
        ∑' c, gamma0PeterssonGramModulusTerm N b a k m n c := by
  simpa only [mul_zero,zero_add] using gamma0PeterssonNormalized_gram N b a k hk hEven m n 0
    (gamma0PeterssonZeroFourierTerm_of_inequivalent N b a h k m n)

end ArtinMatthews
