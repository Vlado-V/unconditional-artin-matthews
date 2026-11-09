module

public import ArtinMatthews.MarkedPhysicalRootResidue


set_option backward.privateInPublic true
@[expose] public section

/-! Partition every primitive point in a positive rectangle by its unique
canonical determinant-one completion and its actual SL2 residue class. -/

noncomputable section
namespace ArtinMatthews
open OAI.Erdos970.ErdosHyperbolaError
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedPhysicalPrimitiveBox (A B C D : ℝ) : Finset (ℤ × ℤ) :=
  ((realIntervalIntegers A B true true).product (realIntervalIntegers C D true true)).filter
    (fun z => IsCoprime z.1 z.2)

theorem markedPhysical_canonical_completion (u v : ℤ) (hu : 0 < u) (hz : IsCoprime u v) :
    ∃ c d : ℤ, 0 ≤ c ∧ c < u ∧ u*d-v*c=1 := by
  obtain ⟨a,b,hab⟩ := hz
  refine ⟨(-b)%u,a-v*((-b)/u),Int.emod_nonneg _ hu.ne',Int.emod_lt_of_pos _ hu,?_⟩
  have he := Int.emod_add_mul_ediv (-b) u
  linear_combination hab-v*he

abbrev MarkedPhysicalCanonicalRoot (S : ℕ) (A B C D : ℝ) :=
  Σ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
    ↥(fixedURootMatrixBoxPoints g A B 0 1 C D true true true true true true)

def markedPhysicalCanonicalRootPosition {S : ℕ} {A B C D : ℝ}
    (r : MarkedPhysicalCanonicalRoot S A B C D) : ℤ × ℤ := fixedURootFirstColumn r.2.1

theorem markedPhysicalCanonicalRootPosition_mem {S : ℕ} {A B C D : ℝ}
    (hA : 1 < A) (hC : 1 < C) (r : MarkedPhysicalCanonicalRoot S A B C D) :
    markedPhysicalCanonicalRootPosition r ∈ markedPhysicalPrimitiveBox A B C D := by
  have hb := fixedURootMatrixBox_coordinate_bounds r.1 A B 0 1 C D true true r.2.1 r.2.2
  have hp := fixedURootMatrixFirstColumns_primitive r.1 hA hC (by norm_num) (by norm_num)
    (Finset.mem_image.mpr ⟨r.2.1,r.2.2,rfl⟩)
  unfold markedPhysicalPrimitiveBox
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hp.2.2⟩
  · exact (fixedURoot_mem_closed_interval A B _).mpr hb.1
  · exact (fixedURoot_mem_closed_interval C D _).mpr hb.2

theorem markedPhysicalCanonicalRootPosition_injective {S : ℕ} [NeZero S]
    {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C) :
    Function.Injective (markedPhysicalCanonicalRootPosition (S := S) (A := A) (B := B) (C := C) (D := D)) := by
  rintro ⟨g,⟨⟨u,c,v⟩,hp⟩⟩ ⟨g',⟨⟨u',c',v'⟩,hp'⟩⟩ he
  have hu : u=u' := congrArg Prod.fst he
  have hv : v=v' := congrArg Prod.snd he
  subst u'
  subst v'
  obtain ⟨d,_,_,hc,hcu,_,_,hd,_⟩ :=
    fixedURootReciprocal_box_canonical hA hC (by norm_num) (by norm_num) hp
  obtain ⟨d',_,_,hc',hcu',_,_,hd',_⟩ :=
    fixedURootReciprocal_box_canonical hA hC (by norm_num) (by norm_num) hp'
  have hcc := fixedURoot_canonical_entry_unique hc.le hcu hc'.le hcu' hd hd'
  subst c'
  have hdd : d=d' := by nlinarith [hd,hd',show 0 < u by linarith]
  subst d'
  obtain ⟨e,he,hg⟩ := fixedURootMatrixBox_integer_root g A B 0 1 C D true true hA hC
    (by norm_num) (by norm_num) ⟨u,(c,v)⟩ hp
  obtain ⟨e',he',hg'⟩ := fixedURootMatrixBox_integer_root g' A B 0 1 C D true true hA hC
    (by norm_num) (by norm_num) ⟨u,(c,v)⟩ hp'
  have hee : e=e' := by
    dsimp [markedMinorIntegerDet] at he he'
    nlinarith [show 0 < u by linarith]
  subst e'
  have hgg : g=g' := hg.symm.trans hg'
  cases hgg
  rfl

theorem markedPhysicalCanonicalRootPosition_surjective {S : ℕ} [NeZero S]
    {A B C D : ℝ} (hA : 1 < A) (hC : 1 < C) :
    ∀ z ∈ markedPhysicalPrimitiveBox A B C D,
      ∃ r : MarkedPhysicalCanonicalRoot S A B C D,markedPhysicalCanonicalRootPosition r=z := by
  rintro ⟨u,v⟩ hz
  unfold markedPhysicalPrimitiveBox at hz
  obtain ⟨hzbox,hzprim⟩ := Finset.mem_filter.mp hz
  obtain ⟨hu,hv⟩ := Finset.mem_product.mp hzbox
  have huR := (fixedURoot_mem_closed_interval A B u).mp hu
  have hvR := (fixedURoot_mem_closed_interval C D v).mp hv
  have huZ : 1 < u := by exact_mod_cast (hA.trans_le huR.1)
  have hvZ : 1 < v := by exact_mod_cast (hC.trans_le hvR.1)
  obtain ⟨c,d,hc,hcu,hd⟩ := markedPhysical_canonical_completion u v (by omega) hzprim
  have hdet : markedMinorIntegerDet (u,v) (c,d)=1 := hd
  let g := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S))
    (markedPhysicalRootMatrix (u,v) (c,d) hdet)
  have hentries : (!![(u : ZMod S),(c : ZMod S);(v : ZMod S),(d : ZMod S)] :
      Matrix (Fin 2) (Fin 2) (ZMod S)) = g := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  obtain ⟨hur,hcr,hvr,hdr⟩ := (fixedURootMatrix_modEq_iff g u c v d).mp hentries
  have hcrange : c ∈ realIntervalIntegers ((u : ℝ)*0) ((u : ℝ)*1) true true := by
    apply (fixedURoot_mem_closed_interval _ _ _).mpr
    simp only [mul_zero,mul_one]
    constructor
    · exact_mod_cast hc
    · exact_mod_cast hcu.le
  have hp : (⟨u,(c,v)⟩ : Σ _u : ℤ,ℤ × ℤ) ∈
      fixedURootMatrixBoxPoints g A B 0 1 C D true true true true true true := by
    apply (fixedURootReciprocal_mem_box (by omega : 0 < u) A B 0 1 C D true true true true true true).mpr
    exact ⟨hu,hcrange,hv,hur,hcr,hvr,d,hd,hdr⟩
  exact ⟨⟨g,⟨⟨u,(c,v)⟩,hp⟩⟩,rfl⟩

def markedPhysicalCanonicalRootEquiv {S : ℕ} [NeZero S] {A B C D : ℝ}
    (hA : 1 < A) (hC : 1 < C) :
    MarkedPhysicalCanonicalRoot S A B C D ≃ ↥(markedPhysicalPrimitiveBox A B C D) :=
  Equiv.ofBijective (fun r => ⟨markedPhysicalCanonicalRootPosition r,
    markedPhysicalCanonicalRootPosition_mem hA hC r⟩)
    ⟨fun _ _ h => markedPhysicalCanonicalRootPosition_injective hA hC (congrArg Subtype.val h),by
      intro z
      obtain ⟨r,hr⟩ := markedPhysicalCanonicalRootPosition_surjective (S := S) hA hC z.1 z.2
      exact ⟨r,Subtype.ext hr⟩⟩

theorem markedPhysicalPrimitiveBox_sum_residues {S : ℕ} [NeZero S] {A B C D : ℝ}
    (hA : 1 < A) (hC : 1 < C) (F : (ℤ × ℤ) → ℂ) :
    (∑ z ∈ markedPhysicalPrimitiveBox A B C D,F z) =
      ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
        ∑ p ∈ fixedURootMatrixBoxPoints g A B 0 1 C D true true true true true true,
          F (fixedURootFirstColumn p) := by
  have h := Equiv.sum_comp (markedPhysicalCanonicalRootEquiv (S := S) (B := B) (D := D) hA hC)
    (fun z => F z.1)
  simp only [markedPhysicalCanonicalRootEquiv,Equiv.ofBijective_apply,Fintype.sum_sigma,
    markedPhysicalCanonicalRootPosition] at h
  rw [Finset.sum_coe_sort] at h
  symm
  calc
    _ = ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
      ∑ p : ↥(fixedURootMatrixBoxPoints g A B 0 1 C D true true true true true true),
        F (fixedURootFirstColumn p.1) := by
      apply Finset.sum_congr rfl
      intro g _
      exact (Finset.sum_coe_sort _ (fun p => F (fixedURootFirstColumn p))).symm
    _ = _ := h

end ArtinMatthews
