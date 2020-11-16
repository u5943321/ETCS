open HolKernel Parse boolLib bossLib;

open ETCSaxiomTheory basicTheory;     

val _ = new_theory "Thm6";


Theorem pb_exists_thm = SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] pb_exists        


val pb_def = new_specification ("pb_def",["pbo","pb1","pb2"],pb_exists_thm)

Theorem iso_symm:
∀X Y. X ≅ Y ⇔ Y ≅ X
Proof
cheat
QED    

Theorem iso_trans:
∀X Y Z. X ≅ Y ∧ Y ≅ Z ⇒ X ≅ Z
Proof
cheat
QED

Theorem iso_to_same:
∀X Y A. X ≅ A ∧ Y ≅ A ⇒ X ≅ Y
Proof
metis_tac[iso_symm,iso_trans]
QED        


    
Theorem inc_inc_iso0:
∀A X Y a b h1 h2. is_mono a ∧ is_mono b ∧ a∶ X → A ∧ b∶ Y → A ∧
                  h1∶ X → Y ∧ h2∶ Y → X ∧
                  b o h1 = a ∧ a o h2 = b ⇒ X ≅ Y
Proof
rw[] >> Cases_on ‘X ≅ zero’ >> Cases_on ‘Y ≅ zero’
>- metis_tac[iso_to_same]
>- metis_tac[to_zero_zero]
>- metis_tac[to_zero_zero]
>- (qabbrev_tac ‘b = a o h2’ >>
   ‘∃b'. b'∶ A → Y ∧ b' o b = id Y’
    by metis_tac[mono_non_zero_post_inv] >>
   ‘∃a'. a'∶ A → X ∧ a' o a = id X’
    by metis_tac[mono_non_zero_post_inv] >>
   simp[are_iso_is_iso] >>
   qexists_tac ‘h1’ >>
   ‘h1 o h2 = id Y ∧ h2 o h1 = id X’
    suffices_by metis_tac[is_iso_thm] >>
   strip_tac (* 2 *)
   >- (‘b' o (a o h2) = id Y’
       by metis_tac[Abbr‘b’] >>
      ‘b' o b o h1 = b' o a’
       by metis_tac[] >>
      ‘h1 = b' o a’ by metis_tac[idL, compose_assoc] >>
      metis_tac[compose_assoc])
   >- (‘a' o a o h2 = a' o b’
       by metis_tac[Abbr‘b’] >>
      ‘h2 = a' o b’ by metis_tac[idL,compose_assoc] >>
      metis_tac[compose_assoc]))
QED


Theorem prop_2_half2:
∀X Y A a b. is_mono a ∧ is_mono b ∧ a∶ X → A ∧ b∶ Y → A ∧
            (∀x xb. x∶ one → A ∧ xb∶ one → X ∧ a o xb = x ⇒
                    ∃xb'. xb'∶ one → Y ∧ b o xb' = x) ⇒
            (∃h. h∶ X → Y ∧ b o h = a)
Proof
rpt strip_tac >> Cases_on ‘Y≅ zero’
>- cheat
>- (‘∃g. g∶ A → Y ∧ g o b = id Y’
    by metis_tac[mono_non_zero_post_inv] >>
   qexists_tac ‘g o a’ >> strip_tac
   >- metis_tac[compose_hom] >> 
   irule fun_ext >>
   ‘b ∘ g ∘ a∶ X → A ∧ a∶ X → A’ by metis_tac[compose_hom] >>
   qexistsl_tac [‘X’,‘A’] >> simp[] >> rpt strip_tac >>
   rename [‘x0∶ one → X’] >>
   first_x_assum (qspecl_then [‘a o x0’,‘x0’] assume_tac) >>
   ‘a o x0∶ one → A’ by metis_tac[compose_hom] >>
   fs[] >> rfs[] >>
   ‘(b ∘ g ∘ a) ∘ x0 = b ∘ g ∘ (a ∘ x0)’
    by metis_tac[compose_assoc_4_3_left] >>
   ‘b ∘ g ∘ a ∘ x0 = b o g o b o xb'’
    by metis_tac[] >>
   ‘b ∘ g ∘ b ∘ xb' = b ∘ (g ∘ b) ∘ xb'’
    by metis_tac[compose_assoc_4_2_left_middle,
                 compose_assoc_4_2_left] >>
   ‘b ∘ (g ∘ b) ∘ xb' = b o xb'’
     by metis_tac[idL] >>
   metis_tac[])
QED


Theorem prop_2_corollary:
∀X Y A a b. a∶ X → A ∧ b∶ Y → A ∧ is_mono a ∧ is_mono b ∧
            (∀y. y∶ one → Y ⇒ ∃x. x∶ one → X ∧ a o x = b o y) ∧
            (∀x. x∶ one → X ⇒ ∃y. y∶ one → Y ∧ a o x = b o y) ⇒
            X ≅ Y
Proof
rw[] >> irule inc_inc_iso0 >>
‘∃h1. h1∶ X → Y ∧ b o h1 = a’
 by (irule prop_2_half2 >> rw[] >> metis_tac[]) >>
‘∃h2. h2∶ Y → X ∧ a o h2 = b’
 by (irule prop_2_half2 >> rw[] >> metis_tac[]) >>
metis_tac[]
QED

        


Definition is_refl_def:
is_refl f0 f1 ⇔ dom f0 = dom f1 ∧ cod f0 = cod f1 ∧
             ∃d. d∶ cod f1 → dom f1 ∧
                 f0 o d = id (cod f1) ∧
                 f1 o d = id (cod f1)
End


Definition is_symm_def:
is_symm f0 f1 ⇔ dom f0 = dom f1 ∧ cod f0 = cod f1 ∧
             ∃t. t∶ dom f1 → dom f1 ∧
                 f0 o t = f1 ∧
                 f1 o t = f0
End


Definition is_trans_def:
is_trans f0 f1 ⇔ dom f0 = dom f1 ∧ cod f0 = cod f1 ∧
                 ∀X h0 h1.
                  h0∶ X → dom f1 ∧ h1∶ X → dom f1 ∧
                  f1 o h0 = f0 o h1 ⇒
                  ∃u. u∶ X → dom f1 ∧
                      f0 o u = f0 o h0 ∧ f1 o u = f1 o h1
End

Theorem Thm6_first_sentence:
∀f0 f1 R A. f0∶ R → A ∧ f1∶ R → A ∧
            is_refl f0 f1 ∧ is_symm f0 f1 ∧ is_trans f0 f1 ∧
            is_mono ⟨f0, f1⟩ ∧
            (∀a0 a1. a0∶ one → A ∧ a1∶ one → A ⇒
                     (coeqa f0 f1) o a0 = (coeqa f0 f1) o a1 ⇔
                     ∃r. r∶ one → R ∧ f0 o r = a0 ∧
                         f1 o r = a1) ⇒
            R ≅ eqo ((coeqa f0 f1) o p1 A A)
                    ((coeqa f0 f1) o p2 A A)
Proof
rw[] >> irule prop_2_corollary >>
qexistsl_tac [‘A × A’,
              ‘⟨f0,f1⟩’,
              ‘eqa (coeqa f0 f1 ∘ p1 A A)
                   (coeqa f0 f1 ∘ p2 A A)’]  >>
‘p1 A A∶ A× A → A ∧ p2 A A∶ A × A → A’
 by metis_tac[p1_hom,p2_hom] >>
‘coeqa f0 f1∶ A → coeqo f0 f1’ by metis_tac[coeqa_hom] >>
‘coeqa f0 f1 o p1 A A∶ (A × A) → coeqo f0 f1 ∧
 coeqa f0 f1 o p2 A A∶ (A × A) → coeqo f0 f1’
  by metis_tac[compose_hom] >>         
‘is_mono (eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A))’
 by metis_tac[eqa_is_mono] >>
‘eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A)∶
  eqo (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) →
  (A × A)’ by metis_tac[eqa_hom] >>
‘⟨f0,f1⟩∶ R → (A × A)’ by metis_tac[pa_hom] >> 
rw[] (* 2 *)
>- (qexists_tac ‘eq_induce (coeqa f0 f1 ∘ p1 A A)
                (coeqa f0 f1 ∘ p2 A A) (⟨f0,f1⟩ o x)’ >>
   ‘(coeqa f0 f1 ∘ p1 A A) ∘ ⟨f0,f1⟩ ∘ x =
   (coeqa f0 f1 ∘ p1 A A ∘ ⟨f0,f1⟩) ∘ x’
    by metis_tac[compose_assoc_4_3_2_left] >>
   ‘(coeqa f0 f1 ∘ p2 A A) ∘ ⟨f0,f1⟩ ∘ x =
    (coeqa f0 f1 ∘ p2 A A ∘ ⟨f0,f1⟩) ∘ x’
    by metis_tac[compose_assoc_4_3_2_left] >>
   ‘p1 A A ∘ ⟨f0,f1⟩ = f0 ∧
    p2 A A ∘ ⟨f0,f1⟩ = f1’ by metis_tac[p1_of_pa,p2_of_pa] >>
   ‘coeqa f0 f1 o f0 = coeqa f0 f1 o f1’
    by metis_tac[coeq_equlity] >>
   ‘eq_induce (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) (⟨f0,f1⟩ ∘ x)∶one →
        eqo (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A)’
     by (irule eq_induce_hom >>
        metis_tac[compose_hom]) >> rw[] >>
   ‘eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) ∘
        eq_induce (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) (⟨f0,f1⟩ ∘ x) = ⟨f0,f1⟩ o x’
     suffices_by metis_tac[] >>
   irule eq_fac >>
   metis_tac[compose_hom])
>- 
 
QED
                                
             

Theorem Thm6:
∀f0 f1 R A. f0∶ R → A ∧ f1∶ R → A ∧
            is_refl f0 f1 ∧ is_symm f0 f1 ∧ is_trans f0 f1 ∧
            is_mono ⟨f0, f1⟩ ⇒
            R ≅ eqo ((coeqa f0 f1) o p1 A A)
                    ((coeqa f0 f1) o p2 A A)
Proof
cheat
QED                    

val _ = export_theory();
