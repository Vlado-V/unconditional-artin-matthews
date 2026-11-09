module

public import ArtinMatthews.GiantMarkedBilinearFinite
public import ArtinMatthews.GiantFixedCharacterReplacement
public import ArtinMatthews.GiantBoundedProgression
public import ArtinMatthews.GiantActualRoughSieve


set_option backward.privateInPublic true
@[expose] public section

/-! Actual fixed-character coefficients in the marked determinant reduction.
The ordinary prime-minus-rough coefficient is the one whose long tests were
proved in `GiantFixedCharacterReplacement`. The remaining input is a bound
on its explicit determinant sum and explicit collision sum. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

def giantMarkedCenteredCore (ε x : ℝ) (u : ℕ) : ℂ :=
  (boundedGiantIndicator u x ε - giantPrimeReciprocalSum x ε : ℝ)

theorem giantMarkedCenteredCore_interface {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, e j < 1) {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) :
    ∀ᶠ x : ℝ in atTop,
      (∀ u, ‖giantMarkedCenteredCore ε x u‖ ≤ 1) ∧
      (∀ j p, p ∈ markedLogPowerBand (e j) x → ∀ u,
        giantMarkedCenteredCore ε x (p*u) = giantMarkedCenteredCore ε x u) := by
  filter_upwards [centered_giant_criterion_interface e he hε hεq] with x hx
  refine ⟨?_, ?_⟩
  · intro u
    simpa only [giantMarkedCenteredCore, Complex.norm_real, Real.norm_eq_abs] using hx.1 u
  · intro j p hp u
    by_cases hu : u = 0
    · simp only [hu, mul_zero]
    · exact congrArg (fun t : ℝ => (t : ℂ)) (hx.2.1 j p hp u (Nat.pos_of_ne_zero hu))

def giantMarkedCharacterEndpointCoefficient {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (W modulation : ℝ) (β : ℕ → ℂ) (s : MarkedTypeIIEndpoint) : ℂ :=
  χ s.value * markedMajorCenteredCoefficient W modulation s.leftFactor * β s.rightFactor *
    giantMarkedLabelDamping P V (s.value - 1)

theorem giantMarkedCharacterEndpointCoefficient_eq {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (W modulation : ℝ) (β : ℕ → ℂ) :
    giantMarkedCharacterEndpointCoefficient P V χ W modulation β =
      giantMarkedEndpointCoefficient P V
        (giantFixedCharacterReplacementCoefficient χ W modulation)
        (fun n => χ n * β n) := by
  funext s
  simp only [giantMarkedCharacterEndpointCoefficient, MarkedTypeIIEndpoint.value,
    Nat.cast_mul, map_mul, giantMarkedEndpointCoefficient,
    giantFixedCharacterReplacementCoefficient]
  ring

/-- Exact determinant input for the genuine ordinary replacement coefficient
and an arbitrary fixed Dirichlet character. Character values at nonunits are
left unchanged; no coprimality condition is introduced. -/
theorem giant_marked_character_norm_sq_le {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (V : J → ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W modulation : ℝ)
    (M N : Finset ℕ) (B : ℕ) (β F : ℕ → ℂ)
    (hM : ∀ m ∈ M, 0 < m) (hN : ∀ n ∈ N, 0 < n)
    (hMN : ∀ a ∈ markedMajorLabelSet P, ∀ m ∈ M, ∀ n ∈ N, m*n ≤ a*B)
    (hF : ∀ j p, p ∈ P j → ∀ h, F (p*h) = F h)
    (hFnorm : ∀ h ∈ Finset.range B, ‖F h‖ ≤ 1) {D C : ℝ}
    (hD : ‖markedTypeIIDeterminantSum (giantMarkedEndpoints P M N)
      (giantMarkedCharacterEndpointCoefficient P V χ W modulation β)‖ ≤ D)
    (hC : ‖markedTypeIICollisionSum (giantMarkedEndpoints P M N) (Finset.range B)
      (giantMarkedCharacterEndpointCoefficient P V χ W modulation β)‖ ≤ C) :
    ‖∑ m ∈ M, ∑ n ∈ N, χ (m*n) * markedMajorCenteredCoefficient W modulation m *
      β n * F (m*n-1) * (divisorWeight Finset.univ P V (m*n-1) : ℂ)‖ ^ 2 ≤
      (B : ℝ) * (D+C) := by
  rw [giantMarkedCharacterEndpointCoefficient_eq] at hD hC
  have hb := giant_marked_bilinear_norm_sq_le P hP hdis V M N B
    (giantFixedCharacterReplacementCoefficient χ W modulation) (fun n => χ n * β n) F
    hM hN hMN hF hFnorm hD hC
  convert hb using 2
  apply congrArg (fun z : ℂ => ‖z‖)
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  simp only [map_mul, giantFixedCharacterReplacementCoefficient]
  ring

/-- The bounded actual giant statistic discharges the invariance and bounded
function assumptions in the preceding finite criterion, simultaneously on
all positive rectangles and all choices of the ordinary coefficients. -/
theorem giant_marked_character_giant_norm_sq_le_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e) (he : ∀ j, e j < 1)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4) :
    ∀ᶠ x : ℝ in atTop, ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ q,
      ∀ W modulation : ℝ, ∀ M N : Finset ℕ, ∀ B : ℕ, ∀ β : ℕ → ℂ,
      (∀ m ∈ M, 0 < m) → (∀ n ∈ N, 0 < n) →
      (∀ a ∈ markedMajorLabelSet (fun j => markedLogPowerBand (e j) x),
        ∀ m ∈ M, ∀ n ∈ N, m*n ≤ a*B) → ∀ D C : ℝ,
      ‖markedTypeIIDeterminantSum (giantMarkedEndpoints (fun j => markedLogPowerBand (e j) x) M N)
        (giantMarkedCharacterEndpointCoefficient (fun j => markedLogPowerBand (e j) x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) χ W modulation β)‖ ≤ D →
      ‖markedTypeIICollisionSum (giantMarkedEndpoints (fun j => markedLogPowerBand (e j) x) M N)
        (Finset.range B) (giantMarkedCharacterEndpointCoefficient (fun j => markedLogPowerBand (e j) x)
          (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) χ W modulation β)‖ ≤ C →
      ‖∑ m ∈ M, ∑ n ∈ N, χ (m*n) * markedMajorCenteredCoefficient W modulation m *
        β n * giantMarkedCenteredCore ε x (m*n-1) *
          (literalMarkedArrayWeight e x (m*n-1) : ℂ)‖ ^ 2 ≤ (B : ℝ) * (D+C) := by
  filter_upwards [giantMarkedCenteredCore_interface e he hε hεq,
    marked_array_disjoint_eventually e hinj] with x hx hdis
  intro q χ W modulation M N B β hM hN hMN D C hD hC
  exact giant_marked_character_norm_sq_le (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) hdis
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) χ W modulation M N B β
    (giantMarkedCenteredCore ε x) hM hN hMN hx.2 (fun h _ => hx.1 h) hD hC

end ArtinMatthews
