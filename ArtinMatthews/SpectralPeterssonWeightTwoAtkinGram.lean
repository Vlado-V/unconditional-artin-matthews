module

public import ArtinMatthews.SpectralPeterssonWeightTwoGram
public import ArtinMatthews.SpectralPeterssonAtkinModuli
public import ArtinMatthews.SpectralPeterssonAtkinPhase


set_option backward.privateInPublic true
@[expose] public section

/-! Exact weight-two same-cusp Gram at the native exact-divisor cusp.
The right horizontal phase agrees with the positive-modulus reindex. -/

noncomputable section
open Set Filter Matrix UpperHalfPlane
open scoped MatrixGroups Topology Manifold ComplexConjugate

namespace ArtinMatthews

theorem gamma0PeterssonWeightTwoAtkin_gram (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (m n : ℕ+) :
    Summable (gamma0PeterssonGramModulusTerm (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) 2 m n) ∧
      gamma0PeterssonInner (r*s) 2 (gamma0PeterssonWeightTwoAtkinNormalized r s hab n)
        (gamma0PeterssonWeightTwoAtkinNormalized r s hab m) =
        (if m=n then 1 else 0)+
          ∑' c, gamma0PeterssonGramModulusTerm (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) 2 m n c := by
  let N := r*s
  let U := gamma0CuspOneOver s
  let F := gamma0PeterssonWeightTwoAtkin r s hab m
  let P := gamma0PeterssonWeightTwoAtkin r s hab n
  let f := gamma0PeterssonWeightTwoInfinity N m
  let d : ℂ := if m=n then 1 else 0
  let V := atkinPhase (((m : ℝ)-(n : ℝ))*((b : ℝ)/(r : ℝ)))
  let W := gamma0PeterssonPositiveModulusTerm N U U 2 m n
  let T := gamma0PeterssonPositiveModulusTerm N 1 1 2 m n
  obtain ⟨M,_,_,hM⟩ := gamma0PeterssonWeightTwoAtkin_weighted_bound r s hcop hab m
  obtain ⟨C,_,hC,_⟩ := gamma0PeterssonWeightTwoAtkin_weighted_bound r s hcop hab n
  have hf (γ : CongruenceSubgroup.Gamma0 N) : spectralHolomorphicSlash 2 (atkinRealMap γ.val) f = f :=
    gamma0PeterssonHecke_limit_slash_gamma0 N 1 m f (gamma0PeterssonWeightTwoInfinity_abel N m) γ
  have hF (γ : CongruenceSubgroup.Gamma0 N) : spectralHolomorphicSlash 2 (atkinRealMap γ.val) F = F :=
    gamma0PeterssonHecke_limit_slash_gamma0 N U m F (gamma0PeterssonWeightTwoAtkin_abel r s hcop hab m) γ
  have hCont : Continuous F := (gamma0PeterssonWeightTwoAtkin_mdifferentiable r s hab m).continuous
  have hseries : (Summable W ↔ Summable T) ∧ (∑' c, W c) = V*(∑' c, T c) :=
    gamma0PeterssonAtkinSameCusp_positiveModulus_reindex r s hcop hab 2 m n
  have hs : Summable W := hseries.1.mpr (gamma0PeterssonWeightTwoFourierAtHeight_geometric N 1 m n 1 zero_lt_one).1
  have hd : V*d = d := by
    by_cases he : m=n
    · subst m
      simp [V,d,atkinPhase]
    · simp [d,he]
  have hA (y : ℝ) (hy : 0 < y) : spectralPeterssonFourierAtHeight
      (spectralHolomorphicSlash 2 (gamma0TrueCuspScaling N U) F) n y hy = d+∑' c, W c := by
    have hper := spectralPeterssonFourierAtHeight_periodic_of_gamma0 N 2 f hf y hy
    have hp : spectralPeterssonFourierAtHeight (spectralHolomorphicSlash 2 (gamma0TrueCuspScaling N U) F) n y hy =
        V*spectralPeterssonFourierAtHeight f n y hy :=
      spectralPeterssonAtkin_sameCusp_FourierAtHeight r s hcop hab 2 f m n y hy hper
    have hg : spectralPeterssonFourierAtHeight f n y hy = d+∑' c, T c := by
      change spectralPeterssonFourierAtHeight (gamma0PeterssonHeckeGrouped N 1 1 0 m) n y hy = _
      rw [(gamma0PeterssonWeightTwoFourierAtHeight_geometric N 1 m n y hy).2,
        gamma0PeterssonZeroFourierTerm_same_chart]
    rw [hp,hg,mul_add,hd,hseries.2]
  have h := gamma0PeterssonInner_hecke_limit_reproduce N U n F P hCont hF M C
    (spectralPeterssonTwo_slash_weighted_bound _ _ hM) (fun u hu z _ => hC u hu z)
    (fun z _ => gamma0PeterssonWeightTwoAtkin_abel r s hcop hab n z) _ hA
  obtain ⟨hS,hGram⟩ := gamma0PeterssonWeightTwo_normalize_gram N U U m n P F d hs h
  refine ⟨hS,?_⟩
  unfold gamma0PeterssonWeightTwoAtkinNormalized
  by_cases he : m=n
  · subst m
    have hroot := (Real.sqrt_pos.mpr (spectralPeterssonReproducingMass_pos 2 le_rfl n)).ne'
    simpa [N,U,F,P,d,hroot] using hGram
  · simpa only [N,U,F,P,d,ite_eq_right he,mul_zero] using hGram

theorem gamma0PeterssonWeightTwoAtkin_negative_gram (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1) (m n : ℕ+) :
    Summable (gamma0PeterssonNegativeGramModulusTerm (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) 2 m n) ∧
      gamma0PeterssonInner (r*s) 2 (fun z => conj (gamma0PeterssonWeightTwoAtkinNormalized r s hab n z))
        (fun z => conj (gamma0PeterssonWeightTwoAtkinNormalized r s hab m z)) =
        (if m=n then 1 else 0)+
          ∑' c, gamma0PeterssonNegativeGramModulusTerm (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) 2 m n c := by
  obtain ⟨hs,h⟩ := gamma0PeterssonWeightTwoAtkin_gram r s hcop hab m n
  have hd : (((if m=n then 1 else 0) : ℝ) : ℂ) = (if m=n then 1 else 0) := by split_ifs <;> simp
  have h' := gamma0PeterssonInner_negative_of_positive (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s)
    2 (by decide) m n _ _ (if m=n then 1 else 0) hs (by rwa [hd])
  simpa only [hd] using h'

end ArtinMatthews
