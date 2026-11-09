module

public import ArtinMatthews.MarkedMemoryHistoryPrimewise


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite SL2 averaging over every chronological vertex. The
prime factors are exactly those of the stated nonzero squarefree modulus.
Coherence is obtained from the literal coefficient, and singleton
baselines are retained once for each modulus prime. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n S : ℕ} [NeZero S] {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

def markedMemoryHistoryCRTRootTest (hS : Squarefree S) (q : ℝ)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℂ :=
  ∏ p : S.primeFactors,
    ((((∏ v ∈ markedMemoryHistoryPrimeVisits hZ history (markedMemoryCRTPrime p),
        markedMemoryRootHit (markedMemoryCRTPrime p) (markedSquarefreeRootCRT hS g p)
          (markedMemoryHistoryVertexPositions hZ history v)) *
      ∏ v ∈ Finset.univ \ markedMemoryHistoryPrimeVisits hZ history (markedMemoryCRTPrime p),
        (1 - markedMemoryEta q n v *
          markedMemoryRootHit (markedMemoryCRTPrime p) (markedSquarefreeRootCRT hS g p)
            (markedMemoryHistoryVertexPositions hZ history v))) : ℝ) : ℂ)

def markedMemoryHistoryCRTAverage (hS : Squarefree S) (q : ℝ) : ℂ :=
  (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℂ)⁻¹ *
    ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S), markedMemoryHistoryCRTRootTest hZ history hS q g

def markedMemoryHistoryCRTPrimeProduct (q : ℝ) : ℂ :=
  ∏ p : S.primeFactors, (markedMemoryHistoryPrimeFactor hZ history q (markedMemoryCRTPrime p) : ℂ)

def markedMemoryHistoryCRTExpansion (q : ℝ) : ℂ :=
  ∏ p : S.primeFactors, (markedMemoryHistoryPrimeExpansion hZ history q (markedMemoryCRTPrime p) : ℂ)

/-- Pure CRT factorization holds for every actual history, without a
nonzero coefficient or distinct-birth hypothesis. -/
theorem markedMemoryHistoryCRT_root_factorization (hS : Squarefree S) (q : ℝ) :
    markedMemoryHistoryCRTAverage hZ history hS q =
      markedMemoryHistoryCRTPrimeProduct (S := S) hZ history q :=
  markedMemoryCRT_root_factorization_slots hS (markedMemoryHistoryVertexSlots hZ history) q
    (markedMemoryHistoryVertexPositions hZ history) (markedMemoryHistoryVertexPrimitive hZ history)

theorem markedMemoryHistoryCRT_baseline_extraction (hS : Squarefree S) (q : ℝ)
    (hb : ∀ p : S.primeFactors, markedMemoryBaseline q n (markedMemoryCRTPrime p) ≠ 0) :
    markedMemoryHistoryCRTAverage hZ history hS q =
      (∏ p : S.primeFactors, (markedMemoryBaseline q n (markedMemoryCRTPrime p) : ℂ)) *
        ∏ p : S.primeFactors,
          (markedMemoryHistoryPrimeFactor hZ history q (markedMemoryCRTPrime p) /
            markedMemoryBaseline q n (markedMemoryCRTPrime p) : ℝ) := by
  rw [markedMemoryHistoryCRT_root_factorization]
  have h := markedMemoryCRT_baseline_extraction q (markedMemoryHistoryVertexPositions hZ history)
    (markedMemoryHistoryVertexPrimitive hZ history)
    (fun p : S.primeFactors => markedMemoryHistoryPrimeVisits hZ history (markedMemoryCRTPrime p)) hb
  have hc := congrArg (fun x : ℝ => (x : ℂ)) h
  simpa only [Complex.ofReal_prod, Complex.ofReal_mul,
    markedMemoryHistoryCRTPrimeProduct, markedMemoryHistoryPrimeFactor] using hc

variable [DecidableEq J]
  (ν : (band : J) → ↥(P band) → ℝ) (V : J → ℝ)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
  (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (j : ℕ)

/-- Every active prime factor uses its actual coherent line; the empty
ones retain the baseline and the strict two-ended orphan sum. -/
theorem markedMemoryHistoryCRT_factorization_expansion (hS : Squarefree S)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history ≠ 0)
    (hempty : ∀ band, (s.2.2.1.1 band : ℕ) = 0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ history) (q : ℝ) :
    markedMemoryHistoryCRTAverage hZ history hS q =
      markedMemoryHistoryCRTExpansion (S := S) hZ history q := by
  rw [markedMemoryHistoryCRT_root_factorization]
  unfold markedMemoryHistoryCRTPrimeProduct markedMemoryHistoryCRTExpansion
  apply Finset.prod_congr rfl
  intro p _
  exact congrArg (fun x : ℝ => (x : ℂ))
    (markedMemoryHistoryPrimeFactor_expansion hZ history ν V ψ η d₀ Y Q ρ qStage χ j
      hw hempty hd q (markedMemoryCRTPrime p))

theorem markedMemoryHistoryCRT_normalized_expansion (hS : Squarefree S)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history ≠ 0)
    (hempty : ∀ band, (s.2.2.1.1 band : ℕ) = 0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ history) (q : ℝ)
    (hb : ∀ p : S.primeFactors, markedMemoryBaseline q n (markedMemoryCRTPrime p) ≠ 0) :
    markedMemoryHistoryCRTAverage hZ history hS q =
      (∏ p : S.primeFactors, (markedMemoryBaseline q n (markedMemoryCRTPrime p) : ℂ)) *
        ∏ p : S.primeFactors,
          (markedMemoryHistoryPrimeExpansion hZ history q (markedMemoryCRTPrime p) /
            markedMemoryBaseline q n (markedMemoryCRTPrime p) : ℝ) := by
  rw [markedMemoryHistoryCRT_baseline_extraction hZ history hS q hb]
  congr 1
  apply congrArg (fun x : ℝ => (x : ℂ))
  apply Finset.prod_congr rfl
  intro p _
  rw [markedMemoryHistoryPrimeFactor_expansion hZ history ν V ψ η d₀ Y Q ρ qStage χ j
    hw hempty hd q (markedMemoryCRTPrime p)]

/-- The zero-weight case is retained, so coefficient-weighted
substitution does not require a separate nonvanishing hypothesis. -/
theorem markedMemoryHistoryCRT_weighted_expansion (hS : Squarefree S)
    (hempty : ∀ band, (s.2.2.1.1 band : ℕ) = 0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ history) (q : ℝ) :
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history *
      markedMemoryHistoryCRTAverage hZ history hS q =
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history *
      markedMemoryHistoryCRTExpansion (S := S) hZ history q := by
  by_cases hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history = 0
  · rw [hw, zero_mul, zero_mul]
  · rw [markedMemoryHistoryCRT_factorization_expansion hZ history ν V ψ η d₀ Y Q ρ qStage χ j
      hS hw hempty hd q]

end
end ArtinMatthews
