module

public import ArtinMatthews.SourceQuadraticDualAdaptiveBound
public import ArtinMatthews.SourceQuadraticDualFullNormalization
public import ArtinMatthews.SourceQuadraticDualDivisorCard


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain QuadraticScale StandardAdelic VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "Bad" => sourceQuadraticBlockBadIdeal F S₀

theorem sourceQuadraticDualErrorBlock_zero {K : ℝ} (hK : K < 1)
    (M σ : ℝ) (cols : Finset E) (u : E → ℂ) (g : E) :
    sourceQuadraticDualErrorBlock F S₀ hζ M K σ cols u g = 0 := by
  have he : quadraticHeckeSquarefreeCutoff F K = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨hsf, hn⟩ := (mem_quadraticHeckeSquarefreeCutoff F).mp ha
    have hp : 0 < Ideal.absNorm a := Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr hsf.ne_zero)
    have hp' : (1:ℝ) ≤ Ideal.absNorm a := by exact_mod_cast (Nat.succ_le_of_lt hp)
    linarith
  simp only [sourceQuadraticDualErrorBlock, sourceQuadraticDualDivisorError,
    sourceQuadraticDualSquarefreeError, he, Finset.sum_empty, mul_zero, Finset.sum_const_zero]

/-- The finite contour error in the literal Full dual expression satisfies
the reciprocal bound, with the actual conductor and all divisor weights. -/
theorem sourceQuadraticDualErrorBlock_bound {α : ℝ} (hα : 1 ≤ α)
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M K P : ℝ, 1 ≤ M → 0 ≤ K → K ≤ M → 1 ≤ P →
      ∀ cols : Finset E,
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ P ≤ (q b : ℝ) ∧ (q b : ℝ) ≤ 2*P) →
      (∀ b ∈ cols, ∀ c ∈ cols,
        sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) →
      ∀ (u : E → ℂ) (g : E),
      ‖sourceQuadraticDualErrorBlock F S₀ hζ M K (quadraticDualErrorLine ε) cols u g‖ ≤
        C * (q g : ℝ)^4 * (M*P)^ε *
          (M+Real.sqrt M*K^(α-1/2)) * coeffMass cols u := by
  obtain ⟨Cr, hCr, hr⟩ := sourceQuadraticDualRestrictedContour_adaptive_bound F S₀ hζ
    hα htrace hE ε hε
  let N : ℝ := Ideal.absNorm Bad
  have hBad : Bad ≠ ⊥ := by
    unfold sourceQuadraticBlockBadIdeal
    exact Ideal.span_singleton_eq_bot.not.mpr
      (SIntegerPrincipalization.principalizingDenominator_ne_zero (sourceHilbertSeed F S₀))
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hBad)
  refine ⟨Cr*N^2, by positivity, ?_⟩
  intro M K P hM hK hKM hP cols hcols hclass u g
  have hG := sourceReflection_norm_one_le F S₀ g
  have hmass : 0 ≤ coeffMass cols u := coeffMass_nonneg _ _
  by_cases hK₁ : 1 ≤ K
  · let D := Cr*(q g : ℝ)*(M*P)^ε*(M+Real.sqrt M*K^(α-1/2))*coeffMass cols u
    have hD : 0 ≤ D := by dsimp [D]; positivity
    let ds := HeckeIdealMobius.divisors F (sourceQuadraticBlockRadical F S₀ g)
    let hs := HeckeIdealMobius.divisors F (quadraticHeckeIdealRadical F Bad)
    have hterm (d : Ideal (𝓞 F)) (hd : d ∈ ds) (h : Ideal (𝓞 F)) (hh : h ∈ hs) :
        ‖sourceQuadraticDualRestrictedContour F S₀ hζ
          (sourceQuadraticDualExteriorRows F S₀ K h) cols u g
          (sourceQuadraticBlockGoodIndex F S₀ g d)
          (M/(Ideal.absNorm d : ℝ)) (Ideal.absNorm h : ℝ) (quadraticDualErrorLine ε)‖ ≤ D := by
      have hdn := sourceQuadraticDual_divisor_norm_one_le F S₀ g d hd
      have hhn := sourceQuadraticDual_bad_norm_one_le F S₀ h hh
      apply hr M K P (M/(Ideal.absNorm d : ℝ)) (Ideal.absNorm h : ℝ)
        hM hK₁ hKM hP (div_pos (zero_lt_one.trans_le hM) (zero_lt_one.trans_le hdn))
        (div_le_self (zero_le_one.trans hM) hdn) hhn _ cols
      · intro a ha
        have ha' := sourceQuadraticDualExteriorRows_spec F S₀ K h a ha
        exact ⟨ha'.1, ha'.2.1⟩
      · exact hcols
      · exact hclass
    have hdc : (ds.card : ℝ) ≤ N*(q g : ℝ) := by
      dsimp only [ds, N]
      exact_mod_cast sourceQuadraticDual_outer_divisor_card F S₀ g
    have hhc : (hs.card : ℝ) ≤ N := by
      dsimp only [hs, N]
      exact_mod_cast sourceQuadraticDual_bad_divisor_card F S₀
    rw [sourceQuadraticDualErrorBlock_eq_restricted F S₀ hζ M K (quadraticDualErrorLine ε)
      cols u g (fun b hb => (hcols b hb).1) hclass]
    calc
      _ ≤ ∑ d ∈ ds, (hs.card : ℝ)*D := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro d hd
        rw [norm_mul]
        have hsum : ‖∑ h ∈ hs, sourceQuadraticDualRestrictedContour F S₀ hζ
            (sourceQuadraticDualExteriorRows F S₀ K h) cols u g
            (sourceQuadraticBlockGoodIndex F S₀ g d)
            (M/(Ideal.absNorm d : ℝ)) (Ideal.absNorm h : ℝ) (quadraticDualErrorLine ε)‖ ≤
              (hs.card : ℝ)*D := by
          apply (norm_sum_le _ _).trans
          calc
            _ ≤ ∑ _h ∈ hs, D := Finset.sum_le_sum (hterm d hd)
            _ = _ := by simp
        exact (mul_le_mul (HeckeIdealMobius.norm_moebius_le_one F d) hsum
          (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      _ = (ds.card : ℝ)*(hs.card : ℝ)*D := by simp [mul_assoc]
      _ ≤ (N*(q g : ℝ))*N*D := by gcongr
      _ = (Cr*N^2)*(q g : ℝ)^2*(M*P)^ε*
          (M+Real.sqrt M*K^(α-1/2))*coeffMass cols u := by dsimp [D]; ring
      _ ≤ _ := by
        gcongr
        norm_num
  · rw [sourceQuadraticDualErrorBlock_zero F S₀ hζ (lt_of_not_ge hK₁), norm_zero]
    positivity

end
end ArtinMatthews.SourceEulerAssembly
