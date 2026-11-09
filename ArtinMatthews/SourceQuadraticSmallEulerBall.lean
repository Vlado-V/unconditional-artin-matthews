module

public import ArtinMatthews.SourceQuadraticSmallEulerMass


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain QuadraticScale StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀

/-- The separated finite row sum retains the actual complete Euler factors. -/
def sourceQuadraticSmallEulerRowSum (rows cols : Finset E) (u : E → ℂ) (s : ℂ) : ℂ :=
  ∑ a ∈ rows, (q a : ℂ) ^ (-(s / 2)) *
    sourceQuadraticSmallCoprimePair F S₀ hζ cols a
      (fun b => u b * star (quadraticSmallEuler F (I b) s))
      (sourceQuadraticSmallEulerCoeff F S₀ u s)

theorem sourceQuadraticSmallRowFactor_norm_le (a : E) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(q a : ℂ) ^ (-(s / 2))‖ ≤ 1 := by
  have hq := sourceReflection_norm_one_le F S₀ a
  rw [← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hq)]
  apply Real.rpow_le_one_of_one_le_of_nonpos hq
  simp only [Complex.neg_re, Complex.div_ofNat_re]
  linarith

variable [IsTotallyComplex F]

theorem sourceQuadraticSmallEulerRowSum_bound {α : ℝ}
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ K P : ℝ, 1 ≤ K → 1 ≤ P → ∀ rows cols : Finset E,
      (∀ a ∈ rows, sourceReflectionIsSquarefree a ∧ (q a : ℝ) ≤ K) →
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ (q b : ℝ) ≤ 2 * P) →
      ∀ (u : E → ℂ) (s : ℂ), 0 ≤ s.re →
      ‖sourceQuadraticSmallEulerRowSum F S₀ hζ rows cols u s‖ ≤
        C * (K * P) ^ η * (2 * P) ^ η * (P + K ^ α) * coeffMass cols u := by
  obtain ⟨Cb, hCb, hb⟩ := sourceQuadraticSmallCoprimePair_ball_bound F S₀ hζ htrace hE η hη
  obtain ⟨Cm, hCm, hm⟩ := sourceQuadraticSmallEulerCoeff_mass F S₀ η hη
  refine ⟨Cb * Cm, by positivity, ?_⟩
  intro K P hK hP rows cols hrows hcols u s hs
  let v := sourceQuadraticSmallEulerCoeff F S₀ u s
  let vl : E → ℂ := fun b => u b * star (quadraticSmallEuler F (I b) s)
  have hmass : 0 ≤ sourceQuadraticSmallWeightedMass F S₀ cols v :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hbound := hb K P hK hP rows cols hrows hcols vl v
  have heq : sourceQuadraticSmallWeightedMass F S₀ cols vl =
      sourceQuadraticSmallWeightedMass F S₀ cols v :=
    sourceQuadraticSmallEulerCoeff_star_mass F S₀ cols u s
  rw [heq, mul_assoc (Cb * (K * P) ^ η * (P + K ^ α)),
    Real.mul_self_sqrt hmass] at hbound
  have hmassBound := hm (2 * P) (by linarith) cols
    (fun b hb' => (hcols b hb').2) u s hs
  calc
    _ ≤ ∑ a ∈ rows, ‖sourceQuadraticSmallCoprimePair F S₀ hζ cols a vl v‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (sourceQuadraticSmallRowFactor_norm_le F S₀ a hs)
    _ ≤ Cb * (K * P) ^ η * (P + K ^ α) * sourceQuadraticSmallWeightedMass F S₀ cols v := hbound
    _ ≤ Cb * (K * P) ^ η * (P + K ^ α) * (Cm * (2 * P) ^ η * coeffMass cols u) :=
      mul_le_mul_of_nonneg_left hmassBound (by positivity)
    _ = _ := by ring

end
end ArtinMatthews.SourceEulerAssembly
