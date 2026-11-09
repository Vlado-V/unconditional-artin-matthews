module

public import ArtinMatthews.SourceQuadraticFourierExpansion
public import ArtinMatthews.SourceQuadraticBalancedRows
public import ArtinMatthews.SourceAdditiveFractionsSieve


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical StandardAdelic VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "S" => sourceHilbertSet F S₀
local notation "OS" => sourceRing F S₀
local notation "E" => ReflectionSquarefreeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "a" => sourcePrimeExponentGenerator F hζ S₀
local notation "ha" => sourcePrimeExponentGenerator_ne_zero F hζ S₀
local notation "L" => SourceReducedFractionLabel F S₀ a

private def sourceQuadraticSieveLabels (cols : Finset E) : Finset L :=
  (cols.image Subtype.val).sigma (fun e => (sourcePoissonQuotientUnitFintype F S₀ hζ e).elems)

private def sourceQuadraticSieveCoefficient (c : E → ℂ) (p : L) : ℂ :=
  if h : ∀ P, p.1 P ≤ 1 then c ⟨p.1, h⟩ *
    sourceQuadraticFourierWeight F S₀ hζ ⟨p.1, h⟩ p.2 else 0

private theorem sourceQuadraticSieveCoefficient_mk (c : E → ℂ) (e : E)
    (d : (OS ⧸ Ideal.span {a e.val})ˣ) :
    sourceQuadraticSieveCoefficient F S₀ hζ c ⟨e.val, d⟩ =
      c e * sourceQuadraticFourierWeight F S₀ hζ e d := by
  unfold sourceQuadraticSieveCoefficient
  exact dite_eq_left e.property

private theorem sourceQuadraticSieveLabels_sum {T : Type} [AddCommMonoid T]
    (cols : Finset E) (f : L → T) :
    (∑ p ∈ sourceQuadraticSieveLabels F S₀ hζ cols, f p) =
      ∑ e ∈ cols, ∑ d ∈ (sourcePoissonQuotientUnitFintype F S₀ hζ e.val).elems, f ⟨e.val, d⟩ := by
  unfold sourceQuadraticSieveLabels
  refine (Finset.sum_sigma _ _ f).trans ?_
  exact Finset.sum_image Subtype.val_injective.injOn

variable [IsTotallyComplex F]

set_option backward.isDefEq.respectTransparency false in
/-- The actual quadratic exterior family has the initial M+N² estimate
on the dyads of the quadratic large sieve. All Fourier mass and row
embedding costs are supplied by the literal source constructions. -/
theorem exists_sourceQuadraticSieve_initial (htrace : traceBadPlaces F ⊆ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N → ∀ (rows cols : Finset E),
      (∀ e ∈ rows, M ≤ (q e.val : ℝ) ∧ (q e.val : ℝ) ≤ 2 * M) →
      (∀ e ∈ cols, (q e.val : ℝ) ≤ N) →
      ∀ c : E → ℂ,
      (∑ e ∈ rows, ‖∑ f ∈ cols,
        c f * reflectionExponentResidueValue F hζ S₀ f.val (a e.val) ^ 3‖ ^ 2) ≤
        C * (M + N ^ 2) * ∑ f ∈ cols, ‖c f‖ ^ 2 := by
  obtain ⟨C, hC, hs⟩ := sourceSeparatedAdditiveFractions_sieve F S₀ hζ htrace
    (sourceQuadraticBalancedBox F S₀ hζ) (sourceQuadraticBalancedBox_isCompact F S₀ hζ)
  refine ⟨C, hC, ?_⟩
  intro M N hM hN rows cols hrows hcols c
  choose b hbI hbU hbM using fun e : rows => exists_sourceQuadraticBalancedRow F S₀ hζ e.val.val
    (zero_lt_one.trans_le hM) (hrows e.val e.property).1 (hrows e.val e.property).2
  have hbinj : Function.Injective b := by
    intro e e' he
    apply Subtype.ext
    apply Subtype.ext
    exact (sourcePrimeExponentRingIdealEquiv F S₀).injective
      (Subtype.ext ((hbI e).trans
        ((congrArg (fun x : OS => (Ideal.span {x} : Ideal OS)) he).trans (hbI e').symm)))
  let A := Finset.univ.map (⟨b, hbinj⟩ : rows ↪ OS)
  let P := sourceQuadraticSieveLabels F S₀ hζ cols
  let w := sourceQuadraticSieveCoefficient F S₀ hζ c
  have hA : ∀ m ∈ A, m ∈ sourceScaledLatticeRows F S₀ hζ (sourceQuadraticBalancedBox F S₀ hζ) M := by
    intro m hm
    obtain ⟨e, _, rfl⟩ := Finset.mem_map.mp hm
    exact hbM e
  have hP : ∀ p ∈ P, (q p.1 : ℝ) ≤ N := by
    intro p hp
    obtain ⟨e, he, he'⟩ := Finset.mem_image.mp (Finset.mem_sigma.mp hp).1
    exact he' ▸ hcols e he
  have h := (hs a ha (sourcePrimeExponentGenerator_ideal F hζ S₀) M N hM hN A P hA hP).1 w
  have hW : (∑ p ∈ P, ‖w p‖ ^ 2) ≤ ∑ f ∈ cols, ‖c f‖ ^ 2 := by
    rw [sourceQuadraticSieveLabels_sum F S₀ hζ cols (fun p => ‖w p‖ ^ 2)]
    apply Finset.sum_le_sum
    intro f _
    have hm := sourceQuadraticFourierWeight_mass F S₀ hζ htrace f
    calc
      _ = ‖c f‖ ^ 2 * ∑ d ∈ (sourcePoissonQuotientUnitFintype F S₀ hζ f.val).elems,
          ‖sourceQuadraticFourierWeight F S₀ hζ f d‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        have hd := sourceQuadraticSieveCoefficient_mk F S₀ hζ c f d
        change ‖sourceQuadraticSieveCoefficient F S₀ hζ c ⟨f.val, d⟩‖ ^ 2 = _
        rw [hd, norm_mul, mul_pow]
      _ ≤ ‖c f‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left hm (sq_nonneg _)
      _ = _ := mul_one _
  have hRow (e : rows) : (∑ f ∈ cols,
      c f * reflectionExponentResidueValue F hζ S₀ f.val (a e.val.val) ^ 3) =
      ∑ p ∈ P, w p * sourceReducedFractionPhase F S₀ a ha p (b e) := by
    rw [sourceQuadraticSieveLabels_sum F S₀ hζ cols
      (fun p => w p * sourceReducedFractionPhase F S₀ a ha p (b e))]
    apply Finset.sum_congr rfl
    intro f _
    obtain ⟨u, hu⟩ := hbU e
    have hres := reflectionExponentResidueValue_mul_sixth F S₀ hζ f.val (a e.val.val) u
    have he : reflectionExponentResidueValue F hζ S₀ f.val (a e.val.val) =
        reflectionExponentResidueValue F hζ S₀ f.val (b e) := hres.symm.trans (by rw [hu])
    have hfour := sourceQuadraticFourierExpansion F S₀ hζ htrace f (b e)
    rw [he, hfour, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    simp only [w, sourceQuadraticSieveCoefficient_mk, mul_assoc]
  rw [show A = Finset.univ.map (⟨b, hbinj⟩ : rows ↪ OS) from rfl, Finset.sum_map] at h
  rw [← Finset.sum_coe_sort rows (fun e : E =>
    ‖∑ f ∈ cols, c f * reflectionExponentResidueValue F hζ S₀ f.val (a e.val) ^ 3‖ ^ 2)]
  simp only [hRow]
  exact h.trans (mul_le_mul_of_nonneg_left hW (by positivity))

end
end ArtinMatthews.SourceEulerAssembly
