module

public import ArtinMatthews.SourceQuadraticDualRestrictedContour
public import ArtinMatthews.QuadraticB3AdaptiveScale
public import ArtinMatthews.SourceQuadraticDualAbsorb
public import ArtinMatthews.SourceQuadraticDualLosses
public import ArtinMatthews.SourceQuadraticDualRestrictedBound
public import ArtinMatthews.SourceQuadraticDualRestrictedShift
public import ArtinMatthews.SourceQuadraticDualRestrictedWeightedBound
public import ArtinMatthews.SourceQuadraticDualScaleBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain QuadraticScale StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

def quadraticDualErrorLine (ε : ℝ) : ℝ := min (ε/4) (1/4)

theorem quadraticDualErrorLine_pos {ε : ℝ} (hε : 0 < ε) : 0 < quadraticDualErrorLine ε :=
  lt_min (by positivity) (by norm_num)

theorem quadraticDualErrorLine_lt_one (ε : ℝ) : quadraticDualErrorLine ε < 1 :=
  (min_le_right _ _).trans_lt (by norm_num)

theorem sourceQuadraticDualRestrictedContour_adaptive_bound {α : ℝ} (hα : 1 ≤ α)
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M K P X B : ℝ,
      1 ≤ M → 1 ≤ K → K ≤ M → 1 ≤ P → 0 < X → X ≤ M → 1 ≤ B →
      ∀ rows cols : Finset E,
      (∀ a ∈ rows, sourceReflectionIsSquarefree a ∧ (q a : ℝ) ≤ K) →
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ P ≤ (q b : ℝ) ∧ (q b : ℝ) ≤ 2*P) →
      (∀ b ∈ cols, ∀ c ∈ cols,
        sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) →
      ∀ (u : E → ℂ) (g d : E),
      ‖sourceQuadraticDualRestrictedContour F S₀ hζ rows cols u g d X B (quadraticDualErrorLine ε)‖ ≤
        C * (q g : ℝ) * (M*P)^ε *
          (M+Real.sqrt M*K^(α-1/2)) * coeffMass cols u := by
  let η := ε/4
  let θ := quadraticDualErrorLine ε
  have hη : 0 < η := by dsimp [η]; positivity
  have hθ : 0 < θ := quadraticDualErrorLine_pos hε
  have hθ₁ : θ < 1 := quadraticDualErrorLine_lt_one ε
  have hτ : 0 < 1-θ := by linarith
  have hτ₁ : 1-θ < 1 := by linarith
  have hloss : 3*η+θ ≤ ε := by
    have h := min_le_left (ε/4) (1/4 : ℝ)
    dsimp [η, θ, quadraticDualErrorLine]
    linarith
  obtain ⟨Cs, hCs, hs⟩ := sourceQuadraticDualRestrictedContour_interval_bound F S₀ hζ
    htrace hE η hη hθ hθ₁
  obtain ⟨Cl, hCl, hl⟩ := sourceQuadraticDualRestrictedContour_weighted_bound F S₀ hζ hα
    htrace hE η hη hτ hτ₁
  obtain ⟨Cd, hCd, hd⟩ := sourceQuadraticDual_dyad_length_bound η hη
  let V := 2+(2:ℝ)^α
  have hV : 0 < V := by dsimp [V]; positivity
  refine ⟨(Cs+Cl*Cd*V)*(2:ℝ)^(2*η), by positivity, ?_⟩
  intro M K P X B hM hK hKM hP hX hXM hB rows cols hrows hcols hclass u g d
  let T := P^2/M
  let small := rows.filter (fun a => (q a : ℝ) ≤ T)
  let large := rows.filter (fun a => ¬ (q a : ℝ) ≤ T)
  let N := M+Real.sqrt M*K^(α-1/2)
  let Z := M*P
  have hM0 := zero_lt_one.trans_le hM
  have hK0 := zero_lt_one.trans_le hK
  have hP0 := zero_lt_one.trans_le hP
  have hG := sourceReflection_norm_one_le F S₀ g
  have hmass : 0 ≤ coeffMass cols u := coeffMass_nonneg _ _
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hscale (σ : ℝ) (hσ : 0 ≤ σ) (hσ₁ : σ ≤ 1) :=
    quadraticDual_conductor_scale_bound hX hXM hP0 hG hσ hσ₁
  have hsmall : ‖sourceQuadraticDualRestrictedContour F S₀ hζ small cols u g d X B θ‖ ≤
      Cs*(q g : ℝ)*(2:ℝ)^(2*η)*Z^ε*N*coeffMass cols u := by
    by_cases he : small = ∅
    · simp only [he, sourceQuadraticDualRestrictedContour, Finset.sum_empty, mul_zero,
        Finset.sum_const_zero, norm_zero]
      positivity
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hT : 1 ≤ T := (sourceReflection_norm_one_le F S₀ a).trans (Finset.mem_filter.mp ha).2
    let A := min K T
    have hA : 1 ≤ A := le_min hK hT
    have hAK : A ≤ K := min_le_left _ _
    have hAT : A ≤ P^2/M := min_le_right _ _
    have hsr (a : E) (ha : a ∈ small) :
        sourceReflectionIsSquarefree a ∧ 1 ≤ (q a : ℝ) ∧ (q a : ℝ) ≤ A := by
      obtain ⟨har, hat⟩ := Finset.mem_filter.mp ha
      exact ⟨(hrows a har).1, sourceReflection_norm_one_le F S₀ a,
        le_min (hrows a har).2 hat⟩
    have hb := hs 1 A P X B (by norm_num) hA hP hX hB small cols hsr hcols hclass u g d
    simp only [Real.one_rpow, mul_one] at hb
    have hscalar := quadraticB3_small_whole_ball_scale hM hP hK hKM
      (zero_lt_one.trans_le hA) hAK hAT hα hθ hθ₁
    have hscaled : X^(1-θ/2)*(P/(q g : ℝ))^(θ-1)*(P+A^α) ≤
        (q g : ℝ)*(Z^θ*N) := by
      calc
        _ ≤ ((q g : ℝ)*M^(1-θ/2)*P^(θ-1))*(P+A^α) :=
          mul_le_mul_of_nonneg_right (hscale θ hθ.le hθ₁.le) (by positivity)
        _ = (q g : ℝ)*(M^(1-θ/2)*P^(θ-1)*(P+A^α)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscalar (by positivity)
    have hpowers := quadraticDual_small_total_power_loss hM hP
      (zero_le_one.trans hA) hAK hKM hη.le hloss
    calc
      _ ≤ Cs*X^(1-θ/2)*(P/(q g : ℝ))^(θ-1)*(A*P)^η*(2*P)^η*(P+A^α)*coeffMass cols u := hb
      _ = (Cs*((A*P)^η*(2*P)^η)*coeffMass cols u)*
          (X^(1-θ/2)*(P/(q g : ℝ))^(θ-1)*(P+A^α)) := by ring
      _ ≤ (Cs*((A*P)^η*(2*P)^η)*coeffMass cols u)*((q g : ℝ)*(Z^θ*N)) :=
        mul_le_mul_of_nonneg_left hscaled (by positivity)
      _ = (Cs*(q g : ℝ)*N*coeffMass cols u)*(((A*P)^η*(2*P)^η)*Z^θ) := by ring
      _ ≤ (Cs*(q g : ℝ)*N*coeffMass cols u)*((2:ℝ)^(2*η)*Z^ε) :=
        mul_le_mul_of_nonneg_left hpowers (by positivity)
      _ = _ := by ring
  have hlarge : ‖sourceQuadraticDualRestrictedContour F S₀ hζ large cols u g d X B (1-θ)‖ ≤
      Cl*Cd*V*(q g : ℝ)*(2:ℝ)^(2*η)*Z^ε*N*coeffMass cols u := by
    let L := max 1 T
    have hL : 1 ≤ L := le_max_left _ _
    have hLT : P^2/M ≤ L := le_max_right _ _
    have hlr (a : E) (ha : a ∈ large) :
        sourceReflectionIsSquarefree a ∧ L ≤ (q a : ℝ) ∧ (q a : ℝ) ≤ K := by
      obtain ⟨har, hat⟩ := Finset.mem_filter.mp ha
      exact ⟨(hrows a har).1,
        max_le (sourceReflection_norm_one_le F S₀ a) (le_of_not_ge hat), (hrows a har).2⟩
    have hb := hl L K P X B (zero_lt_one.trans_le hL) hK hP hX hB
      large cols hlr hcols hclass u g d
    have hscalar := quadraticB3_large_weighted_rows_scale hM hP hK hKM hL hLT hα hθ hθ₁
    simp only [neg_div] at hscalar
    have hweight : 2*P*L^(-((1-θ)/2))+(2:ℝ)^α*K^(α-(1-θ)/2) ≤
        V*(P*L^(-((1-θ)/2))+K^(α-(1-θ)/2)) := by
      dsimp [V]
      nlinarith [Real.rpow_nonneg (zero_le_one.trans hL) (-((1-θ)/2)),
        Real.rpow_nonneg hK0.le (α-(1-θ)/2),
        mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) α)
          (mul_nonneg hP0.le (Real.rpow_nonneg (zero_le_one.trans hL) (-((1-θ)/2))))]
    have hscaled : X^(1-(1-θ)/2)*(P/(q g : ℝ))^((1-θ)-1)*
        (2*P*L^(-((1-θ)/2))+(2:ℝ)^α*K^(α-(1-θ)/2)) ≤
          (q g : ℝ)*V*(Z^θ*N) := by
      calc
        _ ≤ ((q g : ℝ)*M^(1-(1-θ)/2)*P^((1-θ)-1))*
            (V*(P*L^(-((1-θ)/2))+K^(α-(1-θ)/2))) :=
          mul_le_mul (hscale (1-θ) hτ.le hτ₁.le) hweight (by positivity) (by positivity)
        _ = (q g : ℝ)*V*(M^(1-(1-θ)/2)*P^((1-θ)-1)*
            (P*L^(-((1-θ)/2))+K^(α-(1-θ)/2))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscalar (by positivity)
    have hpowers := quadraticDual_weighted_total_power_loss hM hP hK0.le hKM hη.le hloss
      hCd.le (hd M P K hM hP hK hKM)
    calc
      _ ≤ Cl*X^(1-(1-θ)/2)*(P/(q g : ℝ))^((1-θ)-1)*(2*K*P)^η*(2*P)^η*
          (sourceReflectionDyadLength K : ℝ)*
          (2*P*L^(-((1-θ)/2))+(2:ℝ)^α*K^(α-(1-θ)/2))*coeffMass cols u := hb
      _ = (Cl*((2*K*P)^η*(2*P)^η)*(sourceReflectionDyadLength K : ℝ)*coeffMass cols u)*
          (X^(1-(1-θ)/2)*(P/(q g : ℝ))^((1-θ)-1)*
            (2*P*L^(-((1-θ)/2))+(2:ℝ)^α*K^(α-(1-θ)/2))) := by ring
      _ ≤ (Cl*((2*K*P)^η*(2*P)^η)*(sourceReflectionDyadLength K : ℝ)*coeffMass cols u)*
          ((q g : ℝ)*V*(Z^θ*N)) := mul_le_mul_of_nonneg_left hscaled (by positivity)
      _ = (Cl*(q g : ℝ)*V*N*coeffMass cols u)*
          (((2*K*P)^η*(2*P)^η)*(sourceReflectionDyadLength K : ℝ)*Z^θ) := by ring
      _ ≤ (Cl*(q g : ℝ)*V*N*coeffMass cols u)*(Cd*(2:ℝ)^(2*η)*Z^ε) :=
        mul_le_mul_of_nonneg_left hpowers (by positivity)
      _ = _ := by ring
  rw [sourceQuadraticDualRestrictedContour_two_lines F S₀ hζ rows cols u g d hX
    (zero_lt_one.trans_le hB) hθ hθ₁ hτ hτ₁ T]
  exact (norm_add_le _ _).trans ((add_le_add hsmall hlarge).trans_eq (by dsimp [Z, N]; ring))

end
end ArtinMatthews.SourceEulerAssembly
