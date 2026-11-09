module

public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDual


set_option backward.privateInPublic true
@[expose] public section

/-! Identification of the Euclidean dual lattice with the trace-dual
fractional ideal, including the complex-place normalization. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open Module NumberField NumberField.mixedEmbedding
open scoped NumberField nonZeroDivisors Classical BigOperators

noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The actual trace-dual fractional ideal. -/
def mixedTraceDualIdeal : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ I.1) (FractionalIdeal.dual_ne_zero ℤ ℚ I.ne_zero)

/-- Vectors pairing integrally with every vector in the canonical ideal lattice. -/
def mixedEuclideanDualLattice : Submodule ℤ (euclidean.mixedSpace K) where
  carrier := {v | ∀ x ∈ mixedIdealLattice K I,
    ∃ n : ℤ, inner ℝ x v = (n : ℝ)}
  zero_mem' := by intro x _; exact ⟨0, by simp⟩
  add_mem' := by
    intro a b ha hb x hx
    obtain ⟨m, hm⟩ := ha x hx
    obtain ⟨n, hn⟩ := hb x hx
    exact ⟨m + n, by simp [inner_add_right, hm, hn]⟩
  smul_mem' := by
    intro n a ha x hx
    obtain ⟨m, hm⟩ := ha x hx
    refine ⟨n * m, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, hm, Int.cast_mul]

theorem mem_mixedEuclideanDualLattice (v : euclidean.mixedSpace K) :
    v ∈ mixedEuclideanDualLattice K I ↔
      ∀ a : I.1, ∃ n : ℤ, inner ℝ (mixedIdealEmbedding K I a) v = (n : ℝ) := by
  constructor
  · intro h a
    exact h _ ((mem_mixedIdealLattice K I _).mpr ⟨a, rfl⟩)
  · intro h x hx
    obtain ⟨a, rfl⟩ := (mem_mixedIdealLattice K I x).mp hx
    exact h a

theorem mixedTraceTransform_mem_dual_iff (b : K) :
    mixedTraceTransform K (mixedFieldEmbedding K b) ∈ mixedEuclideanDualLattice K I ↔
      b ∈ (mixedTraceDualIdeal K I).1 := by
  rw [mem_mixedEuclideanDualLattice]
  change (∀ a : I.1, ∃ n : ℤ,
    inner ℝ (mixedFieldEmbedding K (a : K))
      (mixedTraceTransform K (mixedFieldEmbedding K b)) = (n : ℝ)) ↔
    b ∈ FractionalIdeal.dual ℤ ℚ I.1
  simp_rw [mixedTraceTransform_inner_eq_trace]
  rw [FractionalIdeal.mem_dual I.ne_zero]
  constructor
  · intro h a ha
    obtain ⟨n, hn⟩ := h ⟨a, ha⟩
    refine ⟨n, ?_⟩
    change (n : ℚ) = Algebra.trace ℚ K (b * a)
    rw [mul_comm]
    exact_mod_cast hn.symm
  · intro h a
    obtain ⟨n, hn⟩ := h a a.property
    refine ⟨n, ?_⟩
    change (n : ℚ) = Algebra.trace ℚ K (b * (a : K)) at hn
    rw [mul_comm] at hn
    exact_mod_cast hn.symm

/-- The trace-dual basis vectors are the Euclidean dual vectors after applying
the explicit trace normalization. -/
theorem mixedTraceDualBasis_pair (i j : MixedIdealIndex K I) :
    inner ℝ (mixedIdealEuclideanBasis K I i)
      (mixedTraceTransform K (mixedFieldEmbedding K
        ((basisOfFractionalIdeal K I).traceDual j))) = if i = j then 1 else 0 := by
  rw [mixedIdealEuclideanBasis_apply]
  change inner ℝ (mixedFieldEmbedding K ((fractionalIdealBasis K I.1 i : I.1) : K)) _ = _
  rw [mixedTraceTransform_inner_eq_trace, ← basisOfFractionalIdeal_apply,
    Basis.trace_mul_traceDual]
  split_ifs <;> norm_num

/-- Every Euclidean dual vector comes from an actual field element of the
trace-dual ideal. This is a surjectivity statement, not merely one inclusion. -/
theorem mem_mixedEuclideanDualLattice_iff_traceDual (v : euclidean.mixedSpace K) :
    v ∈ mixedEuclideanDualLattice K I ↔
      ∃ b : (mixedTraceDualIdeal K I).1,
        mixedTraceTransform K (mixedFieldEmbedding K (b : K)) = v := by
  constructor
  · intro hv
    have hv' := (mem_mixedEuclideanDualLattice K I v).mp hv
    choose z hz using fun i : MixedIdealIndex K I => hv' (fractionalIdealBasis K I.1 i)
    let b : K := ∑ j, z j • (basisOfFractionalIdeal K I).traceDual j
    have heq : v = mixedTraceTransform K (mixedFieldEmbedding K b) := by
      apply InnerProductSpace.ext_inner_left_basis (mixedIdealEuclideanBasis K I)
      intro i
      rw [mixedIdealEuclideanBasis_apply, hz]
      change (z i : ℝ) =
        inner ℝ (mixedFieldEmbedding K ((fractionalIdealBasis K I.1 i : I.1) : K)) _
      rw [mixedTraceTransform_inner_eq_trace, ← basisOfFractionalIdeal_apply]
      simp only [b, Finset.mul_sum, mul_smul_comm, map_sum, map_zsmul,
        Basis.trace_mul_traceDual]
      simp
    have hb : b ∈ (mixedTraceDualIdeal K I).1 :=
      (mixedTraceTransform_mem_dual_iff K I b).mp (heq ▸ hv)
    exact ⟨⟨b, hb⟩, heq.symm⟩
  · rintro ⟨b, rfl⟩
    exact (mixedTraceTransform_mem_dual_iff K I b).mpr b.property

/-- Equality of the complete lattice carriers in the actual Euclidean space. -/
theorem mixedEuclideanDualLattice_eq_traceDual_map :
    mixedEuclideanDualLattice K I =
      (mixedIdealLattice K (mixedTraceDualIdeal K I)).map
        ((mixedTraceTransform K).toLinearMap.restrictScalars ℤ) := by
  ext v
  rw [mem_mixedEuclideanDualLattice_iff_traceDual, Submodule.mem_map]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨mixedFieldEmbedding K (b : K), ?_, hb⟩
    exact (mem_mixedIdealLattice K (mixedTraceDualIdeal K I) _).mpr ⟨b, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨b, rfl⟩ := (mem_mixedIdealLattice K (mixedTraceDualIdeal K I) w).mp hw
    exact ⟨b, rfl⟩

end
end ArtinMatthews.VaryingKummerAnalytic
