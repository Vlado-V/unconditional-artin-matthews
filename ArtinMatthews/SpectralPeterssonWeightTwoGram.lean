module

public import ArtinMatthews.SpectralPeterssonWeightTwo
public import ArtinMatthews.SpectralPeterssonWeightTwoFourier
public import ArtinMatthews.SpectralPeterssonHeckePairingLimit
public import ArtinMatthews.SpectralPeterssonNegativeGram
public import ArtinMatthews.SpectralMixedCuspInequivalent


set_option backward.privateInPublic true
@[expose] public section

/-! The literal weight-two Petersson Gram is obtained by regulated
unfolding and dominated convergence. The normalization agrees with the
higher-weight Gamma convention. -/

noncomputable section
open Set Filter Matrix UpperHalfPlane
open scoped MatrixGroups Topology Manifold ComplexConjugate

namespace ArtinMatthews

def gamma0PeterssonWeightTwoInfinityNormalized (N : ℕ) [NeZero N] (n : ℕ+) (z : UpperHalfPlane) : ℂ :=
  (spectralPeterssonNormalization 2 n : ℂ)*gamma0PeterssonWeightTwoInfinity N n z

def gamma0PeterssonWeightTwoAtkinNormalized (r s : ℕ) [NeZero r] [NeZero s]
    {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (n : ℕ+) (z : UpperHalfPlane) : ℂ :=
  (spectralPeterssonNormalization 2 n : ℂ)*gamma0PeterssonWeightTwoAtkin r s hab n z

theorem gamma0PeterssonWeightTwo_normalize_gram (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (m n : ℕ+) (P F : UpperHalfPlane → ℂ) (d : ℂ)
    (hs : Summable (gamma0PeterssonPositiveModulusTerm N b a 2 m n))
    (h : gamma0PeterssonInner N 2 P F = (spectralPeterssonReproducingMass 2 n : ℂ)*
      (d+∑' c, gamma0PeterssonPositiveModulusTerm N b a 2 m n c)) :
    Summable (gamma0PeterssonGramModulusTerm N b a 2 m n) ∧
      gamma0PeterssonInner N 2 (fun z => (spectralPeterssonNormalization 2 n : ℂ)*P z)
        (fun z => (spectralPeterssonNormalization 2 m : ℂ)*F z) =
        ((Real.sqrt (spectralPeterssonReproducingMass 2 n)/
          Real.sqrt (spectralPeterssonReproducingMass 2 m) : ℝ) : ℂ)*d +
          ∑' c, gamma0PeterssonGramModulusTerm N b a 2 m n c := by
  let u := ((Real.sqrt (spectralPeterssonReproducingMass 2 n)/
    Real.sqrt (spectralPeterssonReproducingMass 2 m) : ℝ) : ℂ)
  have hu : u*((Real.sqrt ((n : ℝ)/(m : ℝ)) : ℝ) : ℂ)^(2-1 : ℕ) = 1 := by
    have h' := congrArg Complex.ofReal (spectralPeterssonNormalization_ratio 2 le_rfl m n)
    simpa only [u,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_one] using h'
  have hterm (c : Ioi (0 : ℕ)) : u*gamma0PeterssonPositiveModulusTerm N b a 2 m n c =
      gamma0PeterssonGramModulusTerm N b a 2 m n c := by
    let _ : NeZero c.val := ⟨c.property.ne'⟩
    dsimp only [gamma0PeterssonPositiveModulusTerm,gamma0PeterssonGramModulusTerm]
    linear_combination (gamma0TrueWidthKloostermanSum N b a c.val (n : ℤ) (m : ℤ)*
      (2*(Real.pi : ℂ)*Complex.I^(-(2 : ℤ))/(gamma0TrueWidthModulus N b a (c.val : ℝ) : ℂ))*
      Complex.besselJ ((2-1 : ℕ) : ℂ)
        (spectralPeterssonBesselArgument m n (gamma0TrueWidthModulus N b a (c.val : ℝ)) : ℂ))*hu
  refine ⟨(hs.mul_left u).congr hterm,?_⟩
  rw [gamma0PeterssonInner_scale_real,h,← mul_assoc,← Complex.ofReal_mul,spectralPeterssonNormalization_mass 2 le_rfl]
  change u*(d+∑' c, gamma0PeterssonPositiveModulusTerm N b a 2 m n c) = _
  rw [mul_add,← tsum_mul_left]
  congr 1
  exact tsum_congr hterm

private theorem peterssonWeightTwoInfinity_pairing (N : ℕ) [NeZero N] (b : SL(2, ℤ))
    (m n : ℕ+) (P : UpperHalfPlane → ℂ) (C : ℝ)
    (hPbd : ∀ u ∈ Ioc (0 : ℝ) 1, ∀ z : UpperHalfPlane, ‖gamma0PeterssonHecke N b u n z‖*z.im ≤ C)
    (hlim : ∀ z : UpperHalfPlane,
      Tendsto (fun u => gamma0PeterssonHecke N b u n z) (𝓝[>] (0 : ℝ)) (𝓝 (P z)))
    (d : ℂ) (h0 : ∀ y (hy : 0 < y), gamma0PeterssonZeroFourierTerm N b 1 2 m n y hy = d) :
    Summable (gamma0PeterssonPositiveModulusTerm N b 1 2 m n) ∧
      gamma0PeterssonInner N 2 P (gamma0PeterssonWeightTwoInfinity N m) =
        (spectralPeterssonReproducingMass 2 n : ℂ)*(d+∑' c, gamma0PeterssonPositiveModulusTerm N b 1 2 m n c) := by
  let F := gamma0PeterssonWeightTwoInfinity N m
  obtain ⟨M,_,_,hM⟩ := gamma0PeterssonWeightTwoInfinity_weighted_bound N m
  have hF (γ : CongruenceSubgroup.Gamma0 N) : spectralHolomorphicSlash 2 (atkinRealMap γ.val) F = F :=
    gamma0PeterssonHecke_limit_slash_gamma0 N 1 m F (gamma0PeterssonWeightTwoInfinity_abel N m) γ
  have hCont : Continuous F := (gamma0PeterssonWeightTwoInfinity_mdifferentiable N m).continuous
  refine ⟨(gamma0PeterssonWeightTwoFourierAtHeight_geometric N b m n 1 zero_lt_one).1,?_⟩
  refine gamma0PeterssonInner_hecke_limit_reproduce N b n F P hCont hF M C
    (spectralPeterssonTwo_slash_weighted_bound _ _ hM) (fun u hu z _ => hPbd u hu z) (fun z _ => hlim z) _ ?_
  intro y hy
  rw [gamma0PeterssonWeightTwoInfinity_slash_cusp,
    (gamma0PeterssonWeightTwoFourierAtHeight_geometric N b m n y hy).2,h0 y hy]

theorem gamma0PeterssonWeightTwoInfinity_gram (N : ℕ) [NeZero N] (m n : ℕ+) :
    Summable (gamma0PeterssonGramModulusTerm N 1 1 2 m n) ∧
      gamma0PeterssonInner N 2 (gamma0PeterssonWeightTwoInfinityNormalized N n)
        (gamma0PeterssonWeightTwoInfinityNormalized N m) =
        (if m=n then 1 else 0)+∑' c, gamma0PeterssonGramModulusTerm N 1 1 2 m n c := by
  obtain ⟨C,_,hC,_⟩ := gamma0PeterssonWeightTwoInfinity_weighted_bound N n
  obtain ⟨hs,h⟩ := peterssonWeightTwoInfinity_pairing N 1 m n _ C hC
    (gamma0PeterssonWeightTwoInfinity_abel N n) (if m=n then 1 else 0)
    (gamma0PeterssonZeroFourierTerm_same_chart N 1 2 m n)
  obtain ⟨hss,hG⟩ := gamma0PeterssonWeightTwo_normalize_gram N 1 1 m n _ _ _ hs h
  refine ⟨hss,?_⟩
  unfold gamma0PeterssonWeightTwoInfinityNormalized
  by_cases he : m=n
  · subst m
    simpa only [gamma0PeterssonWeightTwoInfinityNormalized,ite_eq_left rfl,
      div_self (ne_of_gt (Real.sqrt_pos.mpr (spectralPeterssonReproducingMass_pos 2 le_rfl n))),
      Complex.ofReal_one,one_mul] using hG
  · simpa only [gamma0PeterssonWeightTwoInfinityNormalized,ite_eq_right he,mul_zero] using hG

theorem gamma0PeterssonWeightTwoInfinity_negative_gram (N : ℕ) [NeZero N] (m n : ℕ+) :
    Summable (gamma0PeterssonNegativeGramModulusTerm N 1 1 2 m n) ∧
      gamma0PeterssonInner N 2 (fun z => conj (gamma0PeterssonWeightTwoInfinityNormalized N n z))
        (fun z => conj (gamma0PeterssonWeightTwoInfinityNormalized N m z)) =
        (if m=n then 1 else 0)+∑' c, gamma0PeterssonNegativeGramModulusTerm N 1 1 2 m n c := by
  obtain ⟨hs,h⟩ := gamma0PeterssonWeightTwoInfinity_gram N m n
  have hd : (((if m=n then 1 else 0) : ℝ) : ℂ) = (if m=n then 1 else 0) := by split_ifs <;> simp
  have h' := gamma0PeterssonInner_negative_of_positive N 1 1 2 (by decide) m n _ _
    (if m=n then 1 else 0) hs (by rwa [hd])
  simpa only [hd] using h'

theorem gamma0PeterssonWeightTwoMixed_gram (r s : ℕ) [NeZero r] [NeZero s]
    (hr : 1 < r) (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (m n : ℕ+) :
    Summable (gamma0PeterssonGramModulusTerm (r*s) (gamma0CuspOneOver s) 1 2 m n) ∧
      gamma0PeterssonInner (r*s) 2 (gamma0PeterssonWeightTwoAtkinNormalized r s hab n)
        (gamma0PeterssonWeightTwoInfinityNormalized (r*s) m) =
        ∑' c, gamma0PeterssonGramModulusTerm (r*s) (gamma0CuspOneOver s) 1 2 m n c := by
  obtain ⟨C,_,hC,_⟩ := gamma0PeterssonWeightTwoAtkin_weighted_bound r s hcop hab n
  obtain ⟨hs,h⟩ := peterssonWeightTwoInfinity_pairing (r*s) (gamma0CuspOneOver s) m n _ C hC
    (gamma0PeterssonWeightTwoAtkin_abel r s hcop hab n) 0
    (gamma0PeterssonZeroFourierTerm_of_inequivalent (r*s) _ 1
      (gamma0MixedCusps_inequivalent_of_one_lt r s hr) 2 m n)
  unfold gamma0PeterssonWeightTwoAtkinNormalized gamma0PeterssonWeightTwoInfinityNormalized
  simpa only [mul_zero,zero_add] using gamma0PeterssonWeightTwo_normalize_gram (r*s) (gamma0CuspOneOver s) 1 m n _ _ 0 hs h

theorem gamma0PeterssonWeightTwoMixed_negative_gram (r s : ℕ) [NeZero r] [NeZero s]
    (hr : 1 < r) (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (m n : ℕ+) :
    Summable (gamma0PeterssonNegativeGramModulusTerm (r*s) (gamma0CuspOneOver s) 1 2 m n) ∧
      gamma0PeterssonInner (r*s) 2 (fun z => conj (gamma0PeterssonWeightTwoAtkinNormalized r s hab n z))
        (fun z => conj (gamma0PeterssonWeightTwoInfinityNormalized (r*s) m z)) =
        ∑' c, gamma0PeterssonNegativeGramModulusTerm (r*s) (gamma0CuspOneOver s) 1 2 m n c := by
  obtain ⟨hs,h⟩ := gamma0PeterssonWeightTwoMixed_gram r s hr hcop hab m n
  simpa only [Complex.ofReal_zero,zero_add] using
    gamma0PeterssonInner_negative_of_positive (r*s) (gamma0CuspOneOver s) 1 2 (by decide) m n _ _ 0 hs
      (by simpa only [Complex.ofReal_zero,zero_add] using h)

end ArtinMatthews
