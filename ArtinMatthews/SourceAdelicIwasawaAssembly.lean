module

public import ArtinMatthews.SourceKPRingBorel
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import ArtinMatthews.SourceKPIwasawaMatrices
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.SelbergSieve
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

/-! Local integral matrix families define genuine finite adelic matrices.
The Iwasawa choices are trivial in the Borel and scalar coordinates whenever
the input matrix is integral. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup Filter
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K]

def sourceKPAdeleMatrixFamily
    (g : (P : HeightOneSpectrum (𝓞 K)) → GL (Fin 2) (P.adicCompletion K))
    (hg : ∀ᶠ P in cofinite, SourceKPIntegralMatrix (sourceKPFiniteVal K P) (g P)) :
    GL (Fin 2) 𝔸ᶠ[K] := by
  let m : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K] := fun i j =>
    ⟨fun P => g P i j, hg.mono (fun P hP =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P).mpr (hP.entries i j))⟩
  let n : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K] := fun i j =>
    ⟨fun P => (g P)⁻¹ i j, hg.mono (fun P hP =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P).mpr
        ((sourceKPIntegralMatrix_inv (sourceKPFiniteVal K P) hP).entries i j))⟩
  refine ⟨m, n, ?_, ?_⟩
  · apply Matrix.ext
    intro i j
    apply FiniteAdeleRing.ext
    intro P
    have h := congrArg (fun a : GL (Fin 2) (P.adicCompletion K) => a i j) (mul_inv_cancel (g P))
    change (sourceKPAdeleEval K P) ((m * n) i j) = (sourceKPAdeleEval K P) ((1 : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K]) i j)
    simp only [Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]
    have h_one : (sourceKPAdeleEval K P) ((1 : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K]) i j) =
        (1 : Matrix (Fin 2) (Fin 2) (P.adicCompletion K)) i j := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [h_one]
    change (g P) i 0 * ((g P)⁻¹ : GL (Fin 2) (P.adicCompletion K)) 0 j +
      (g P) i 1 * ((g P)⁻¹ : GL (Fin 2) (P.adicCompletion K)) 1 j = _
    simpa only [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_one, Matrix.mul_apply, Fin.sum_univ_two] using h
  · apply Matrix.ext
    intro i j
    apply FiniteAdeleRing.ext
    intro P
    have h := congrArg (fun a : GL (Fin 2) (P.adicCompletion K) => a i j) (inv_mul_cancel (g P))
    change (sourceKPAdeleEval K P) ((n * m) i j) = (sourceKPAdeleEval K P) ((1 : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K]) i j)
    simp only [Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]
    have h_one : (sourceKPAdeleEval K P) ((1 : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[K]) i j) =
        (1 : Matrix (Fin 2) (Fin 2) (P.adicCompletion K)) i j := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [h_one]
    change ((g P)⁻¹ : GL (Fin 2) (P.adicCompletion K)) i 0 * (g P) 0 j +
      ((g P)⁻¹ : GL (Fin 2) (P.adicCompletion K)) i 1 * (g P) 1 j = _
    simpa only [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_one, Matrix.mul_apply, Fin.sum_univ_two] using h

theorem sourceKPAdeleMatrixFamily_at
    (g : (P : HeightOneSpectrum (𝓞 K)) → GL (Fin 2) (P.adicCompletion K))
    (hg : ∀ᶠ P in cofinite, SourceKPIntegralMatrix (sourceKPFiniteVal K P) (g P))
    (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPAdeleMatrixAt K P (sourceKPAdeleMatrixFamily K g hg) = g P := by
  apply GeneralLinearGroup.ext
  intro i j
  rfl

theorem sourceKPAdeleMatrixAt_ext {g h : GL (Fin 2) 𝔸ᶠ[K]}
    (he : ∀ P, sourceKPAdeleMatrixAt K P g = sourceKPAdeleMatrixAt K P h) : g = h := by
  apply GeneralLinearGroup.ext
  intro i j
  apply FiniteAdeleRing.ext
  intro P
  exact congrArg (fun a : GL (Fin 2) (P.adicCompletion K) => a i j) (he P)

structure SourceKPLocalIwasawaData (P : HeightOneSpectrum (𝓞 K))
    (g : GL (Fin 2) (P.adicCompletion K)) where
  borel : GL (Fin 2) (P.adicCompletion K)
  scalar : (P.adicCompletion K)ˣ
  integral : GL (Fin 2) (P.adicCompletion K)
  borel_mem : borel ∈ sourceGL2NormalizedBorel (P.adicCompletion K)
  integral_mem : SourceKPIntegralMatrix (sourceKPFiniteVal K P) integral
  factor : g = borel * GeneralLinearGroup.scalar (Fin 2) scalar * integral

def sourceKPLocalIwasawa (P : HeightOneSpectrum (𝓞 K))
    (g : GL (Fin 2) (P.adicCompletion K)) : SourceKPLocalIwasawaData K P g := by
  classical
  by_cases hg : SourceKPIntegralMatrix (sourceKPFiniteVal K P) g
  · exact ⟨1, 1, g, (sourceGL2NormalizedBorel _).one_mem, hg, by simp⟩
  · exact Classical.choice (show Nonempty (SourceKPLocalIwasawaData K P g) from by
      obtain ⟨b, d, k, hb, hk, he⟩ := sourceKPIwasawa_matrix_factor (sourceKPFiniteVal K P) g
      exact ⟨⟨b, d, k, hb, hk, he⟩⟩)

theorem sourceKPLocalIwasawa_of_integral (P : HeightOneSpectrum (𝓞 K))
    (g : GL (Fin 2) (P.adicCompletion K))
    (hg : SourceKPIntegralMatrix (sourceKPFiniteVal K P) g) :
    (sourceKPLocalIwasawa K P g).borel = 1 ∧
      (sourceKPLocalIwasawa K P g).scalar = 1 ∧
      (sourceKPLocalIwasawa K P g).integral = g := by
  simp only [sourceKPLocalIwasawa, dite_eq_left hg, and_self]

def sourceKPAdeleLocalIwasawa (g : GL (Fin 2) 𝔸ᶠ[K]) (P : HeightOneSpectrum (𝓞 K)) :=
  sourceKPLocalIwasawa K P (sourceKPAdeleMatrixAt K P g)

theorem sourceKPAdeleIwasawa_eventually_trivial (g : GL (Fin 2) 𝔸ᶠ[K]) :
    ∀ᶠ P in cofinite, (sourceKPAdeleLocalIwasawa K g P).borel = 1 ∧
      (sourceKPAdeleLocalIwasawa K g P).scalar = 1 ∧
      (sourceKPAdeleLocalIwasawa K g P).integral = sourceKPAdeleMatrixAt K P g :=
  (sourceKPAdeleMatrixAt_eventually_integral K g).mono (fun P hP =>
    sourceKPLocalIwasawa_of_integral K P _ hP)

def sourceKPAdeleIwasawaBorel (g : GL (Fin 2) 𝔸ᶠ[K]) : GL (Fin 2) 𝔸ᶠ[K] :=
  sourceKPAdeleMatrixFamily K (fun P => (sourceKPAdeleLocalIwasawa K g P).borel)
    ((sourceKPAdeleIwasawa_eventually_trivial K g).mono (fun P hP => by
      rw [hP.1]
      exact sourceKPIntegralMatrix_one _))

def sourceKPAdeleIwasawaIntegral (g : GL (Fin 2) 𝔸ᶠ[K]) : GL (Fin 2) 𝔸ᶠ[K] :=
  sourceKPAdeleMatrixFamily K (fun P => (sourceKPAdeleLocalIwasawa K g P).integral)
    (Eventually.of_forall (fun P => (sourceKPAdeleLocalIwasawa K g P).integral_mem))

def sourceKPAdeleIwasawaScalar (g : GL (Fin 2) 𝔸ᶠ[K]) : 𝔸ᶠ[K]ˣ := by
  let d := fun P => (sourceKPAdeleLocalIwasawa K g P).scalar
  have hd : ∀ᶠ P in cofinite, d P = 1 :=
    (sourceKPAdeleIwasawa_eventually_trivial K g).mono (fun _ hP => hP.2.1)
  let a : 𝔸ᶠ[K] := ⟨fun P => (d P : P.adicCompletion K), hd.mono (fun P hP => by
    change (d P : P.adicCompletion K) ∈ P.adicCompletionIntegers K
    rw [hP]
    exact (P.adicCompletionIntegers K).one_mem)⟩
  let b : 𝔸ᶠ[K] := ⟨fun P => ((d P)⁻¹ : P.adicCompletion K), hd.mono (fun P hP => by
    change ((d P)⁻¹ : P.adicCompletion K) ∈ P.adicCompletionIntegers K
    simp only [hP, Units.val_one, inv_one]
    exact (P.adicCompletionIntegers K).one_mem)⟩
  refine ⟨a, b, ?_, ?_⟩ <;> apply FiniteAdeleRing.ext <;> intro P
  · change (d P : P.adicCompletion K) * ((d P)⁻¹ : P.adicCompletion K) = 1
    exact mul_inv_cancel₀ (d P).ne_zero
  · change ((d P)⁻¹ : P.adicCompletion K) * (d P : P.adicCompletion K) = 1
    exact inv_mul_cancel₀ (d P).ne_zero

theorem sourceKPAdeleIwasawaBorel_at (g : GL (Fin 2) 𝔸ᶠ[K]) (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPAdeleMatrixAt K P (sourceKPAdeleIwasawaBorel K g) =
      (sourceKPAdeleLocalIwasawa K g P).borel := sourceKPAdeleMatrixFamily_at K _ _ P

theorem sourceKPAdeleIwasawaIntegral_at (g : GL (Fin 2) 𝔸ᶠ[K]) (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPAdeleMatrixAt K P (sourceKPAdeleIwasawaIntegral K g) =
      (sourceKPAdeleLocalIwasawa K g P).integral := sourceKPAdeleMatrixFamily_at K _ _ P

theorem sourceKPAdeleIwasawaScalar_at (g : GL (Fin 2) 𝔸ᶠ[K]) (P : HeightOneSpectrum (𝓞 K)) :
    Units.map (sourceKPAdeleEval K P) (sourceKPAdeleIwasawaScalar K g) =
      (sourceKPAdeleLocalIwasawa K g P).scalar := by
  apply Units.ext
  rfl

theorem sourceKPAdeleIwasawaBorel_mem (g : GL (Fin 2) 𝔸ᶠ[K]) :
    sourceKPAdeleIwasawaBorel K g ∈ sourceKPRingNormalizedBorel 𝔸ᶠ[K] := by
  constructor
  · apply FiniteAdeleRing.ext
    intro P
    exact congrArg (fun a : GL (Fin 2) (P.adicCompletion K) => a 1 0)
      (sourceKPAdeleIwasawaBorel_at K g P) |>.trans (sourceKPAdeleLocalIwasawa K g P).borel_mem.1
  · apply FiniteAdeleRing.ext
    intro P
    exact congrArg (fun a : GL (Fin 2) (P.adicCompletion K) => a 1 1)
      (sourceKPAdeleIwasawaBorel_at K g P) |>.trans (sourceKPAdeleLocalIwasawa K g P).borel_mem.2

theorem sourceKPAdeleIwasawaIntegral_mem (g : GL (Fin 2) 𝔸ᶠ[K]) (P : HeightOneSpectrum (𝓞 K)) :
    SourceKPIntegralMatrix (sourceKPFiniteVal K P)
      (sourceKPAdeleMatrixAt K P (sourceKPAdeleIwasawaIntegral K g)) := by
  rw [sourceKPAdeleIwasawaIntegral_at]
  exact (sourceKPAdeleLocalIwasawa K g P).integral_mem

theorem sourceKPAdeleIwasawa_factor (g : GL (Fin 2) 𝔸ᶠ[K]) :
    g = sourceKPAdeleIwasawaBorel K g *
      GeneralLinearGroup.scalar (Fin 2) (sourceKPAdeleIwasawaScalar K g) *
        sourceKPAdeleIwasawaIntegral K g := by
  apply sourceKPAdeleMatrixAt_ext K
  intro P
  rw [map_mul, map_mul]
  change sourceKPAdeleMatrixAt K P g = sourceKPAdeleMatrixAt K P (sourceKPAdeleIwasawaBorel K g) *
    GeneralLinearGroup.map (sourceKPAdeleEval K P)
      (GeneralLinearGroup.scalar (Fin 2) (sourceKPAdeleIwasawaScalar K g)) * _
  rw [GeneralLinearGroup.map_scalar, sourceKPAdeleIwasawaScalar_at,
    sourceKPAdeleIwasawaBorel_at, sourceKPAdeleIwasawaIntegral_at]
  exact (sourceKPAdeleLocalIwasawa K g P).factor

end
end ArtinMatthews
