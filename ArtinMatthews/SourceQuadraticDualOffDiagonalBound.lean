module

public import ArtinMatthews.SourceQuadraticDualAdaptiveBound
public import ArtinMatthews.SourceQuadraticDualErrorIntegral
public import ArtinMatthews.SourceQuadraticDualErrorBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

def sourceQuadraticDualOffDiagonalErrorBlock (M K σ : ℝ) (cols : Finset E)
    (u : E → ℂ) (g : E) : ℂ :=
  ∑ p ∈ (cols ×ˢ cols).filter (fun p : E×E => p.1 ⊓ p.2 = g ∧ p.1 ≠ p.2),
    star (u p.1)*u p.2*sourceQuadraticDualDivisorError F S₀ hζ M K σ g ((p.1-g)+(p.2-g))

theorem sourceQuadraticDualErrorBlock_diagonal_split (M K σ : ℝ)
    (cols : Finset E) (u : E → ℂ) (g : E) :
    sourceQuadraticDualErrorBlock F S₀ hζ M K σ cols u g =
      sourceQuadraticDualOffDiagonalErrorBlock F S₀ hζ M K σ cols u g +
      sourceQuadraticDualErrorBlock F S₀ hζ M K σ (cols.filter (fun b => b=g)) u g := by
  let ps := (cols ×ˢ cols).filter (fun p : E×E => p.1 ⊓ p.2 = g)
  let D := cols.filter (fun b => b=g)
  have ho : ps.filter (fun p : E×E => p.1 ≠ p.2) =
      (cols ×ˢ cols).filter (fun p : E×E => p.1 ⊓ p.2 = g ∧ p.1 ≠ p.2) := by
    ext p
    simp [ps, and_assoc]
  have hd : ps.filter (fun p : E×E => ¬p.1 ≠ p.2) =
      (D ×ˢ D).filter (fun p : E×E => p.1 ⊓ p.2 = g) := by
    ext p
    rcases p with ⟨b,c⟩
    simp only [ps, D, Finset.mem_filter, Finset.mem_product, not_not]
    constructor
    · rintro ⟨⟨⟨hb,hc⟩, hi⟩, he⟩
      subst c
      have hbg : b=g := by simpa using hi
      exact ⟨⟨⟨hb,hbg⟩,⟨hb,hbg⟩⟩,hi⟩
    · rintro ⟨⟨⟨hb,hbg⟩,⟨hc,hcg⟩⟩,hi⟩
      exact ⟨⟨⟨hb,hc⟩,hi⟩,hbg.trans hcg.symm⟩
  have h := Finset.sum_filter_add_sum_filter_not ps (fun p : E×E => p.1 ≠ p.2)
    (fun p => star (u p.1)*u p.2*
      sourceQuadraticDualDivisorError F S₀ hζ M K σ g ((p.1-g)+(p.2-g)))
  rw [ho,hd] at h
  exact h.symm

theorem sourceQuadraticDualOffDiagonalErrorBlock_bound {α : ℝ} (hα : 1 ≤ α)
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M K P : ℝ, 1 ≤ M → 0 ≤ K → K ≤ M → 1 ≤ P →
      ∀ cols : Finset E,
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ P ≤ (q b : ℝ) ∧ (q b : ℝ) ≤ 2*P) →
      (∀ b ∈ cols, ∀ c ∈ cols,
        sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c) →
      ∀ (u : E → ℂ) (g : E),
      ‖sourceQuadraticDualOffDiagonalErrorBlock F S₀ hζ M K (quadraticDualErrorLine ε) cols u g‖ ≤
        C*(q g : ℝ)^4*(M*P)^ε*(M+Real.sqrt M*K^(α-1/2))*coeffMass cols u := by
  obtain ⟨C,hC,hbound⟩ := sourceQuadraticDualErrorBlock_bound F S₀ hζ hα htrace hE ε hε
  refine ⟨2*C,by positivity,?_⟩
  intro M K P hM hK hKM hP cols hcols hclass u g
  let D := cols.filter (fun b => b=g)
  have hD : D ⊆ cols := Finset.filter_subset _ _
  have hm : coeffMass D u ≤ coeffMass cols u :=
    Finset.sum_le_sum_of_subset_of_nonneg hD (fun _ _ _ => sq_nonneg _)
  have hwhole := hbound M K P hM hK hKM hP cols hcols hclass u g
  have hdiag := hbound M K P hM hK hKM hP D (fun b hb => hcols b (hD hb))
    (fun b hb c hc => hclass b (hD hb) c (hD hc)) u g
  have he := sourceQuadraticDualErrorBlock_diagonal_split F S₀ hζ M K
    (quadraticDualErrorLine ε) cols u g
  have hoff : sourceQuadraticDualOffDiagonalErrorBlock F S₀ hζ M K
      (quadraticDualErrorLine ε) cols u g =
    sourceQuadraticDualErrorBlock F S₀ hζ M K (quadraticDualErrorLine ε) cols u g -
      sourceQuadraticDualErrorBlock F S₀ hζ M K (quadraticDualErrorLine ε) D u g := by
    rw [he]
    ring
  rw [hoff]
  apply (norm_sub_le _ _).trans
  calc
    _ ≤ C*(q g : ℝ)^4*(M*P)^ε*(M+Real.sqrt M*K^(α-1/2))*coeffMass cols u +
        C*(q g : ℝ)^4*(M*P)^ε*(M+Real.sqrt M*K^(α-1/2))*coeffMass D u :=
      add_le_add hwhole hdiag
    _ ≤ C*(q g : ℝ)^4*(M*P)^ε*(M+Real.sqrt M*K^(α-1/2))*coeffMass cols u +
        C*(q g : ℝ)^4*(M*P)^ε*(M+Real.sqrt M*K^(α-1/2))*coeffMass cols u := by
      gcongr
    _ = _ := by ring

end
end ArtinMatthews.SourceEulerAssembly
