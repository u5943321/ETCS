open HolKernel Parse boolLib bossLib;

open ETCSaxiomTheory basicTheory;     

open Thm3Theory Thm5Theory;

     
val _ = new_theory "Thm6";

    
val _ = overload_on("two", “one + one”);


Theorem pb_exists_thm = SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] pb_exists        


val pb_def = new_specification ("pb_def",["pbo","pb1","pb2"],pb_exists_thm)

Theorem iso_symm:
∀X Y. X ≅ Y ⇔ Y ≅ X
Proof
rw[] >> simp[are_iso_is_iso] >> metis_tac[is_iso_thm]
QED    

Theorem iso_compose_iso:
∀X Y Z f g. is_iso f ∧ is_iso g ∧ f∶ X → Y ∧ g∶ Y → Z ⇒
            is_iso (g o f)
Proof
rw[] >>
‘∃f'. f'∶ Y → X ∧ f' o f = id X ∧ f o f' = id Y’
 by metis_tac[is_iso_thm] >>
‘∃g'. g'∶ Z → Y ∧ g' o g = id Y ∧ g o g' = id Z’
 by metis_tac[is_iso_thm] >>
‘g o f∶ X → Z’ by metis_tac[compose_hom] >>
drule is_iso_thm >> rw[] >>
qexists_tac ‘f' o g'’ >>
‘f' o g'∶ Z → X’ by metis_tac[compose_hom] >> simp[] >>
‘(f' ∘ g') ∘ g ∘ f = f' ∘ (g' ∘ g) ∘ f’
 by metis_tac[compose_assoc_4_2_left_middle] >>
‘(g ∘ f) ∘ f' ∘ g' = g ∘ (f ∘ f') ∘ g'’
 by metis_tac[compose_assoc_4_2_left_middle] >>
simp[] >> metis_tac[idL,idR]
QED    
       
Theorem iso_trans:
∀X Y Z. X ≅ Y ∧ Y ≅ Z ⇒ X ≅ Z
Proof
rw[are_iso_is_iso] >> qexists_tac ‘f' o f’ >> metis_tac[compose_hom,iso_compose_iso]
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
(*a function taking an arrow and give its hom?
 a program given two arrows and show  they are eq via assoc*)
(*
Theorem iso_zero_iso_zero_hom:
∀X Y. X ≅ zero ∧ Y ≅ zero ⇒ ∃h. X → Y
Proof
*)

Theorem prop_2_half2:
∀X Y A a b. is_mono a ∧ is_mono b ∧ a∶ X → A ∧ b∶ Y → A ∧
            (∀x xb. x∶ one → A ∧ xb∶ one → X ∧ a o xb = x ⇒
                    ∃xb'. xb'∶ one → Y ∧ b o xb' = x) ⇒
            (∃h. h∶ X → Y ∧ b o h = a)
Proof
rpt strip_tac >> Cases_on ‘Y≅ zero’
>- (‘X ≅ zero’
     by
      (SPOSE_NOT_THEN ASSUME_TAC >>
      ‘∃x. x∶ one → X’ by metis_tac[ax6] >>
      ‘a o x∶ one → A’ by metis_tac[compose_hom] >>
      ‘∃xb'. xb'∶one → Y’ by metis_tac[] >>
      metis_tac[iso_zero_no_mem]) >>
   fs[are_iso_is_iso] >>
   ‘∃f''. f''∶zero → Y ∧ f'' ∘ f = id Y ∧ f ∘ f'' = id zero’
    by metis_tac[is_iso_thm] >>
   qexists_tac ‘f'' o f'’ >>
   ‘f'' ∘ f'∶X → Y’ by metis_tac[compose_hom] >> simp[] >>
   irule from_iso_zero_eq >> qexistsl_tac [‘X’,‘A’] >>
   metis_tac[compose_hom,are_iso_is_iso])    
>- (‘∃g. g∶ A → Y ∧ g o b = id Y’ >>
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
            (∀a0 a1. a0∶ one → A ∧ a1∶ one → A ∧
                     (coeqa f0 f1) o a0 = (coeqa f0 f1) o a1 ⇒
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
>- (first_x_assum (qspecl_then
   [‘p1 A A o eqa (coeqa f0 f1 ∘ p1 A A)
                  (coeqa f0 f1 ∘ p2 A A) ∘ y’,
    ‘p2 A A o eqa (coeqa f0 f1 ∘ p1 A A)
                  (coeqa f0 f1 ∘ p2 A A) ∘ y’] assume_tac) >>
   ‘p2 A A ∘ eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) ∘ y∶one → A ∧
    p1 A A ∘ eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) ∘ y∶one → A’ by metis_tac[compose_hom] >>
   ‘coeqa f0 f1 ∘ p1 A A ∘
    eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) ∘ y =
    (coeqa f0 f1 ∘ p1 A A ∘
    eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A)) ∘ y ∧
    coeqa f0 f1 ∘ p2 A A ∘
    eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) ∘ y =
    (coeqa f0 f1 ∘ p2 A A ∘
    eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A)) ∘ y’
    by metis_tac[compose_assoc_4_3_left] >>
   ‘(coeqa f0 f1 ∘ p1 A A ∘
         eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A)) =
    (coeqa f0 f1 ∘ p2 A A ∘
         eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A))’
    by metis_tac[eq_equlity,compose_assoc] >>
   ‘∃r.r∶one → R ∧
        f0 ∘ r =
        p1 A A ∘ eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) ∘ y ∧
        f1 ∘ r =
        p2 A A ∘ eqa (coeqa f0 f1 ∘ p1 A A) (coeqa f0 f1 ∘ p2 A A) ∘ y’ by metis_tac[] >>
   qexists_tac ‘r’ >>
   ‘⟨f0,f1⟩ ∘ r∶ one → (A × A) ∧
    eqa (coeqa f0 f1 ∘ p1 A A)
        (coeqa f0 f1 ∘ p2 A A) ∘ y∶ one → (A × A)’
     by metis_tac[compose_hom] >>
   rw[] >>
   irule to_p_eq_applied >> qexistsl_tac [‘A’,‘A’,‘one’] >>
   simp[] >> metis_tac[compose_assoc,p1_of_pa,p2_of_pa])
QED
(*

Theorem Thm5:
∀A X a. is_mono a ∧ a∶ A → X ⇒
        ∃A' a'. is_mono a' ∧ a'∶ A' → X ∧ is_iso (copa a a')
Proof
cheat
QED*)

(*need to delete it if can open Thm5Theory*)        

Theorem char_exists:
∀a. is_mono a ⇒ ∃phi. phi∶ cod a → (one + one) ∧
    ∀x. x∶ one → cod a ⇒ ((∃x0. x0∶ one → dom a ∧ a o x0 = x) ⇔
                         phi o x = i2 one one)
Proof
rw[] >>
drule Thm5 >> rw[] >>
qabbrev_tac ‘A = dom a’ >> qabbrev_tac ‘X = cod a’ >>
‘a∶ A → X’ by metis_tac[hom_def] >>
first_x_assum drule >> rw[] >>
‘copa a a'∶ A + A' → X’ by metis_tac[copa_hom] >>
drule is_iso_thm >> rw[] >>
‘i2 one one o to1 A∶ A → one + one’
 by metis_tac[i2_hom,to1_hom,compose_hom] >>
‘i1 one one o to1 A'∶ A' → one + one’
 by metis_tac[i1_hom,to1_hom,compose_hom] >>
‘copa (i2 one one o to1 A) (i1 one one o to1 A')∶ A + A' → one + one’
 by metis_tac[copa_hom] >>
rename [‘ copa a a' ∘ f = id X’] >>
‘copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') o f∶ X → one + one’
 by metis_tac[compose_hom] >>
qexists_tac ‘copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') o f’ >>
simp[] >> rw[] >>
rw[EQ_IMP_THM] (*2  *)
>- (‘copa a a' o i1 A A' = a’ by metis_tac[i1_of_copa] >>
   ‘f o copa a a' o i1 A A' = (f o copa a a') o i1 A A'’
    by metis_tac[i1_hom,compose_assoc] >>
   ‘f o a = i1 A A'’ by metis_tac[idL,i1_hom] >>
   ‘(copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ f) ∘ a ∘ x0 =
    copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ (f ∘ a) ∘ x0’
    by metis_tac[compose_assoc_4_2_left_middle] >>
   simp[] >>
   ‘copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ i1 A A' ∘ x0 =
    (copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ i1 A A') ∘ x0’
    by metis_tac[i1_hom,compose_assoc] >>
   simp[] >>
   ‘copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ i1 A A' =
    (i2 one one ∘ to1 A)’ by metis_tac[i1_of_copa] >>
   simp[] >>
   ‘(i2 one one ∘ to1 A) ∘ x0 = i2 one one ∘ to1 A ∘ x0’
    by metis_tac[compose_assoc,to1_hom,i2_hom] >>
   ‘to1 A o x0 = id one’
    by metis_tac[compose_hom,to1_hom,id1,to1_unique] >>
   simp[] >> metis_tac[i2_hom,idR])
>- (‘f o x∶ one → A + A'’ by metis_tac[compose_hom] >>
   drule to_copa_fac >> rw[] (* 2 *)
   >- (‘a = copa a a' o i1 A A'’ by metis_tac[i1_of_copa] >>
      qexists_tac ‘x0’ >> simp[] >>
      ‘copa a a' ∘ i1 A A' o x0 = x’
       suffices_by metis_tac[i1_hom,compose_assoc] >>
      simp[] >>
      metis_tac[idL,compose_assoc])
   >- (‘(copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ f) ∘ x =
       i1 one one’ suffices_by metis_tac[i1_ne_i2] >>
      ‘(copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ f) ∘ x =
       copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ f ∘ x’
       by metis_tac[compose_assoc] >>
      ‘copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ i2 A A' ∘ x0' = i1 one one’ suffices_by metis_tac[] >>
      ‘copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ i2 A A' ∘ x0' = (copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ i2 A A') ∘ x0'’
       by metis_tac[i2_hom,compose_assoc] >>
      simp[] >>
      ‘copa (i2 one one ∘ to1 A) (i1 one one ∘ to1 A') ∘ i2 A A' =
       i1 one one o to1 A'’ by metis_tac[i2_of_copa] >>
      simp[] >>
      ‘(i1 one one ∘ to1 A') ∘ x0' = i1 one one ∘ to1 A' ∘ x0'’
       by metis_tac[i1_hom,compose_assoc,to1_hom] >>
      simp[] >>
      ‘to1 A' ∘ x0' = id one’
       by metis_tac[to1_hom,compose_hom,id1,to1_unique] >>
      metis_tac[idR,i1_hom]))
QED
     

Theorem char_exists_thm = SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] char_exists        

val char_def = new_specification ("char_def",["char"],char_exists_thm)
(*
Theorem sing_exists:
∀A. ∃s. s∶ A → exp A 2 ∧
    ∀x y. x∶ one → A ∧ y∶ one → A ⇒
    (∃y0. y0∶ one → eqo () ((i2 one one) o (to1 A))) ⇔
    y = x
        *)


Theorem char_thm:
∀a A X.
    is_mono a ∧ a∶ A → X ⇒
         char a∶ X → one + one ∧
         ∀x.
             x∶one → X ⇒
             ((∃x0. x0∶one → A ∧ a ∘ x0 = x) ⇔ char a ∘ x = i2 one one)
Proof
strip_tac >> strip_tac >> strip_tac >> strip_tac >>
fs[hom_def] >> metis_tac[char_def,hom_def]
QED

        (*

Definition n2a_def:
n2a f = 

(*n2a sends a 1 --> 2^A  to transpose, a2n other direction*)

  ev A (one + one) o ⟨p1 A one, hb o tp (psi o p2 one R)⟩
*)


Theorem fac_char:
∀m A X. is_mono m ∧ m∶ A → X ⇒
        ∀P p f. p∶ P → X ∧ f∶ P → A ∧ m o f = p ⇒
                char m o p = (i2 one one) ∘ to1 P
Proof
rw[] >> drule char_thm >> rw[] >>
first_x_assum drule >> rw[] >>
‘char m ∘ m ∘ f∶ P → two ∧ i2 one one o to1 P∶ P → two’
 by metis_tac[compose_hom,i2_hom,to1_hom] >>
irule fun_ext >> qexistsl_tac [‘P’,‘two’] >> simp[] >>
rw[] >>
‘(char m ∘ m ∘ f) ∘ a = char m ∘ m ∘ f ∘ a’
 by (irule compose_assoc_4_3_left >> metis_tac[]) >>
rw[] >>
‘m o f o a∶ one → X’ by metis_tac[compose_hom] >>
first_x_assum drule >> rw[] >>
‘f o a∶ one → A’ by metis_tac[compose_hom] >>
‘(i2 one one ∘ to1 P) ∘ a = i2 one one ∘ to1 P ∘ a’
 by metis_tac[compose_assoc,i2_hom,to1_hom] >>
simp[] >>
‘to1 P o a = id one’
 by metis_tac[to1_hom,compose_hom,id1,to1_unique] >>
simp[] >> metis_tac[i2_hom,idR]
QED

(*match one lemma with inverse direction*)        

Theorem iso_zero_zero:
∀A. A≅ zero ⇒
   ∀X. ∃!f. f∶ A → X
Proof
rw[EXISTS_UNIQUE_ALT] >>
‘∃i. i∶A → zero ∧ is_iso i’ by metis_tac[are_iso_is_iso] >>
qexists_tac ‘(from0 X) o i’ >>
rw[EQ_IMP_THM] >> metis_tac[from_iso_zero_eq,ax1_2,compose_hom]
QED

Theorem epi_has_section:
∀e A B. is_epi e ∧ e∶ A → B ⇒ ∃s. s∶ B → A ∧ e o s = id B
Proof
rw[] >> Cases_on ‘B ≅ zero’
>- (drule iso_zero_zero >> rw[] >>
   fs[EXISTS_UNIQUE_ALT] >>
   ‘∃f. ∀f'. f'∶B → A ⇔ f = f'’ by metis_tac[] >>
   qexists_tac ‘f’ >>
   metis_tac[id1,compose_hom])
>- metis_tac[epi_pre_inv]
QED

        

Theorem fac_char_via_any_map:
∀f A B M m e b. is_epi e ∧ is_mono m ∧ f = m o e ∧
              f∶ A → B ∧ e∶ A → M ∧ m∶ M → B ∧
              b∶ one → B ∧ (char m) o b = i2 one one ⇒
              ∃a. a∶ one → A ∧ f o a = b
Proof
rw[] >> drule epi_has_section >> rw[] >>
first_x_assum drule >> rw[] >>
drule char_thm >> rw[] >> first_x_assum drule >> rw[] >>
first_x_assum (qspec_then ‘b’ assume_tac) >> rfs[] >>
qexists_tac ‘s' o x0’ >>
‘s' o x0 ∶ one → A’ by metis_tac[compose_hom] >> simp[] >>
‘(m ∘ e) ∘ s' ∘ x0 = m ∘ (e ∘ s') ∘ x0’
 by metis_tac[compose_assoc_4_2_left_middle] >>
metis_tac[idL,idR]
QED

Theorem fac_through_eq:
∀f g h h0 A B X. f∶ A → B ∧ g∶ A → B ∧ h∶ X → A ∧ h0∶ X → eqo f g ∧
           eqa f g o h0 = h ⇒
           f o h = g o h
Proof
rw[] >>
‘eqa f g∶ eqo f g → A’ by metis_tac[eqa_hom] >>
‘f ∘ eqa f g ∘ h0 = (f ∘ eqa f g) ∘ h0 ∧
 g ∘ eqa f g ∘ h0 = (g ∘ eqa f g) ∘ h0’
  by metis_tac[compose_assoc] >>
‘f ∘ eqa f g = g ∘ eqa f g’
 suffices_by metis_tac[compose_assoc] >>
metis_tac[eq_equlity]
QED

Theorem fac_through_eq_iff:
∀f g h. f∶ A → B ∧ g∶ A → B ∧ h∶ X → A ⇒
        ((∃h0. h0∶ X → eqo f g ∧ (eqa f g) o h0 = h) ⇔
         f o h = g o h)
Proof
rw[EQ_IMP_THM] (* 2 *)
>- metis_tac[fac_through_eq]
>- (qexists_tac ‘eq_induce f g h’ >> metis_tac[eq_induce_hom,eq_fac])
QED

           
Theorem mem_of_name_eqa:
∀psi R r. psi∶ R → two ∧ r∶ one → R ⇒
               (psi o r = i2 one one ⇔
                ∃r'. r'∶ one → eqo (ev R two) (i2 one one o to1 (R × exp R two)) ∧
                    eqa (ev R two) (i2 one one o to1 (R × exp R two)) o r' = ⟨r, tp (psi ∘ p1 R one)⟩)
Proof
rw[] >>
‘ev R two∶ (R × (exp R two)) → two’ by metis_tac[ev_hom] >>
‘to1 (R × exp R two)∶ (R × (exp R two)) → one’
 by metis_tac[to1_hom] >>
‘i2 one one∶ one → two’ by metis_tac[i2_hom] >>
‘p1 R one∶ (R × one) → R’ by metis_tac[p1_hom] >>
‘psi o p1 R one∶ (R × one) → two’ by metis_tac[compose_hom] >>
‘tp (psi ∘ p1 R one)∶ one → exp R two’ by metis_tac[tp_hom] >>
‘⟨r,tp (psi ∘ p1 R one)⟩∶one → (R × (exp R two))’
 by metis_tac[pa_hom] >> 
‘(i2 one one ∘ to1 (R × exp R two))∶ (R × (exp R two)) → two’
 by metis_tac[compose_hom] >> 
‘(∃r'.
                 r'∶one → eqo (ev R two) (i2 one one ∘ to1 (R × exp R two)) ∧
                 eqa (ev R two) (i2 one one ∘ to1 (R × exp R two)) ∘ r' =
                 ⟨r,tp (psi ∘ p1 R one)⟩) ⇔
   (ev R two) o ⟨r,tp (psi ∘ p1 R one)⟩ = (i2 one one ∘ to1 (R × exp R two)) o ⟨r,tp (psi ∘ p1 R one)⟩’
  by (irule fac_through_eq_iff >> metis_tac[]) >>
rw[] >>
‘(i2 one one ∘ to1 (R × exp R two)) ∘ ⟨r,tp (psi ∘ p1 R one)⟩ =
 i2 one one ∘ to1 (R × exp R two) ∘ ⟨r,tp (psi ∘ p1 R one)⟩’
 by metis_tac[compose_assoc] >>
‘to1 (R × exp R two) ∘ ⟨r,tp (psi ∘ p1 R one)⟩ = id one’
 by (irule to1_unique >> metis_tac[id1,compose_hom]) >>
simp[] >>
‘i2 one one ∘ id one = i2 one one’ by metis_tac[idR] >>
simp[] >> metis_tac[tp_element_ev]
QED

Theorem compose_with_id_to1:
∀x A. x∶ one → A ⇒ ⟨id A,to1 A⟩ ∘ x = ⟨x, id one⟩
Proof
rw[] >>
‘id A∶ A → A ∧ to1 A∶ A → one’ by metis_tac[to1_hom,id1] >>
‘⟨id A,to1 A⟩∶ A → (A × one)’ by metis_tac[pa_hom] >>
‘⟨id A,to1 A⟩ ∘ x∶ one → (A × one)’ by metis_tac[compose_hom] >>
‘id one∶ one → one’ by metis_tac[id1] >>
‘⟨x,id one⟩∶ one → (A × one)’ by metis_tac[pa_hom] >>
irule to_p_eq_applied >>
qexistsl_tac [‘A’,‘one’,‘one’] >> simp[] >>
‘p1 A one ∘ ⟨id A,to1 A⟩ o x = (p1 A one ∘ ⟨id A,to1 A⟩) o x ∧
 p2 A one ∘ ⟨id A,to1 A⟩ o x = (p2 A one ∘ ⟨id A,to1 A⟩) o x’
 by metis_tac[p1_hom,p2_hom,compose_assoc] >>
simp[] >>
‘(p1 A one ∘ ⟨id A,to1 A⟩) = id A ∧
 p1 A one o ⟨x, id one⟩ = x’ by metis_tac[p1_of_pa] >>
‘(p2 A one ∘ ⟨id A,to1 A⟩) = to1 A ∧
 p2 A one o ⟨x, id one⟩ = id one’ by metis_tac[p2_of_pa] >>
simp[] >> metis_tac[to1_unique,idL,compose_hom]
QED


Theorem ev_compose_split:
∀A B X Y f g. g∶ X → exp A Y ∧ f∶ B → X  ⇒
          (ev A Y) o ⟨p1 A B, g o f o p2 A B⟩ = 
          ((ev A Y) o ⟨p1 A X, g o p2 A X⟩) o
           ⟨p1 A B,f o p2 A B⟩
Proof
rw[] >>
‘ev A Y∶ (A × exp A Y) → Y’ by metis_tac[ev_hom] >>
‘p1 A X∶ (A × X) → A ∧ p2 A X∶ (A × X) → X ∧
 p1 A B∶ (A × B) → A ∧ p2 A B∶ (A × B) → B’
 by metis_tac[p1_hom,p2_hom] >>
‘g o p2 A X∶ (A × X) → exp A Y ∧ f o p2 A B∶ (A × B) → X’
 by metis_tac[compose_hom] >>
‘⟨p1 A B,f ∘ p2 A B⟩∶ (A × B) → (A × X)’ by metis_tac[pa_hom] >>
‘⟨p1 A X,g ∘ p2 A X⟩∶ (A × X) → (A × exp A Y)’
 by metis_tac[pa_hom] >>
‘(ev A Y ∘ ⟨p1 A X,g ∘ p2 A X⟩) ∘ ⟨p1 A B,f ∘ p2 A B⟩ =
 ev A Y ∘ ⟨p1 A X,g ∘ p2 A X⟩ ∘ ⟨p1 A B,f ∘ p2 A B⟩’
 by metis_tac[compose_assoc,pa_hom] >>
‘⟨p1 A B,g ∘ f ∘ p2 A B⟩ =
 ⟨p1 A X,g ∘ p2 A X⟩ ∘ ⟨p1 A B,f ∘ p2 A B⟩’
 suffices_by metis_tac[] >>
irule parallel_p_one_side >> metis_tac[]
QED

Theorem two_steps_compose_combine:
∀A X Y f g. f∶ X → A ∧ g∶ X → Y ⇒
       ⟨p1 A X,g o p2 A X⟩ o ⟨f, id X⟩ = ⟨f,g⟩
Proof
rw[] >>
‘p1 A X∶ (A × X) → A ∧ p2 A X∶ (A × X) → X ∧ id X∶ X → X’
 by metis_tac[p1_hom,p2_hom,id1] >>
‘g o p2 A X∶ (A × X) → Y’ by metis_tac[compose_hom] >>
irule to_p_eq_applied >> qexistsl_tac [‘A’,‘Y’,‘X’] >>
‘⟨p1 A X,g ∘ p2 A X⟩∶ (A × X) → (A × Y)’ by metis_tac[pa_hom] >>
‘⟨f,id X⟩∶ X → (A × X)’ by metis_tac[pa_hom] >>
‘⟨f,g⟩∶ X → (A × Y)’ by metis_tac[pa_hom] >>
‘p1 A Y ∘ ⟨p1 A X,g ∘ p2 A X⟩ ∘ ⟨f,id X⟩ =
 (p1 A Y ∘ ⟨p1 A X,g ∘ p2 A X⟩) ∘ ⟨f,id X⟩’
 by metis_tac[p1_hom,compose_assoc] >>
‘p2 A Y ∘ ⟨p1 A X,g ∘ p2 A X⟩ ∘ ⟨f,id X⟩ =
 (p2 A Y ∘ ⟨p1 A X,g ∘ p2 A X⟩) ∘ ⟨f,id X⟩’
 by metis_tac[p2_hom,compose_assoc] >>
‘(p1 A Y ∘ ⟨p1 A X,g ∘ p2 A X⟩) = p1 A X’
 by metis_tac[p1_of_pa] >>
‘(p2 A Y ∘ ⟨p1 A X,g ∘ p2 A X⟩) = g ∘ p2 A X’
 by metis_tac[p2_of_pa] >>
simp[] >>
‘(g ∘ p2 A X) ∘ ⟨f,id X⟩ = g ∘ p2 A X ∘ ⟨f,id X⟩’
 by metis_tac[compose_assoc] >>
simp[] >>
‘p2 A X ∘ ⟨f,id X⟩ = id X’ by metis_tac[p2_of_pa] >>
simp[] >> metis_tac[p1_of_pa,p2_of_pa,idR,compose_hom]
QED
        
        
Theorem compose_partial_ev:
∀A X Y x psi ϕ.
  x∶ one → A ∧ psi∶ X → Y ∧ ϕ∶ (A × exp X Y) → Y ⇒ 
             ϕ ∘ ⟨x,tp (psi ∘ p1 X one)⟩ =
             ev A Y ∘ ⟨p1 A one,tp ϕ ∘ tp (psi ∘ p1 X one) o p2 A one⟩ ∘
             ⟨id A,to1 A⟩ ∘ x
Proof
rw[] >>
‘tp ϕ∶ exp X Y → exp A Y’ by metis_tac[tp_hom] >>
drule ev_compose_split  >> strip_tac >>
‘p1 X one∶ (X × one) → X’ by metis_tac[p1_hom] >>
‘psi o p1 X one∶ (X × one) → Y’ by metis_tac[compose_hom] >>
‘tp (psi o p1 X one)∶ one → exp X Y’ by metis_tac[tp_hom] >>
first_x_assum drule >> rw[] >>
‘⟨id A,to1 A⟩ ∘ x =  ⟨x, id one⟩’
 by metis_tac[compose_with_id_to1] >>
simp[] >>
‘p1 A one∶ (A × one) → A ∧ p2 A one∶ (A × one) → one’
 by metis_tac[p1_hom,p2_hom] >>
‘tp ϕ ∘ tp (psi ∘ p1 X one) ∘ p2 A one∶ (A × one) → exp A Y’
 by metis_tac[compose_hom] >>
‘⟨p1 A one,tp ϕ ∘ tp (psi ∘ p1 X one) ∘ p2 A one⟩∶
 (A × one) → (A × exp A Y)’ by metis_tac[pa_hom] >>
‘⟨x,id one⟩∶ one → (A × one)’ by metis_tac[id1,pa_hom] >>
‘ev A Y∶ (A × exp A Y) → Y’ by metis_tac[ev_hom] >>
‘ev A Y ∘ ⟨p1 A one,tp ϕ ∘ tp (psi ∘ p1 X one) ∘ p2 A one⟩ ∘
        ⟨x,id one⟩ =
 (ev A Y ∘ ⟨p1 A one,tp ϕ ∘ tp (psi ∘ p1 X one) ∘ p2 A one⟩) ∘
        ⟨x,id one⟩’ by metis_tac[compose_assoc] >>
simp[] >>
‘ev A Y ∘ ⟨p1 A (exp X Y),tp ϕ ∘ p2 A (exp X Y)⟩ = ϕ’
 by metis_tac[ev_of_tp] >>
simp[] >>
‘tp (psi ∘ p1 X one) ∘ p2 A one∶ (A × one) → exp X Y’
 by metis_tac[compose_hom] >>
‘(ϕ ∘ ⟨p1 A one,tp (psi ∘ p1 X one) ∘ p2 A one⟩) ∘ ⟨x,id one⟩ =
  ϕ ∘ ⟨p1 A one,tp (psi ∘ p1 X one) ∘ p2 A one⟩ ∘ ⟨x,id one⟩’
  by metis_tac[compose_assoc,pa_hom] >>
simp[] >>
‘⟨x,tp (psi ∘ p1 X one)⟩ =
 ⟨p1 A one,tp (psi ∘ p1 X one) ∘ p2 A one⟩ ∘ ⟨x,id one⟩’
 suffices_by metis_tac[] >>
metis_tac[two_steps_compose_combine]
QED
        
Theorem Thm6_lemma_3:
∀h R A. h∶ R → A ⇒
        ∃hb. hb∶ exp R (one + one) → exp A (one + one) ∧
             (∀psi. psi∶ R → one + one ⇒
                    ∀x. x∶ one → A ⇒
                        (ev A (one + one) o ⟨p1 A one, hb o tp (psi o p1 R one) o p2 A one⟩ o ⟨id A, to1 A⟩ o x = i2 one one ⇔
                         ∃r. r∶ one → R ∧
                             psi o r = i2 one one ∧
                             h o r = x))
Proof
rw[] >>
‘ev R two∶ (R × (exp R two)) → two’ by metis_tac[ev_hom] >>
qabbrev_tac ‘i₀ = i1 one one’ >>
qabbrev_tac ‘i₁ = i2 one one’ >>
‘i₀∶  one → two ∧ i₁∶ one → two’
 by (simp[Abbr‘i₀’,Abbr‘i₁’] >>
    metis_tac[i1_hom,i2_hom]) >>
‘to1 (R × (exp R two))∶ (R × (exp R two)) → one’
 by metis_tac[to1_hom] >>
‘i₁ o to1 (R × (exp R two))∶ (R × (exp R two)) → two’
 by metis_tac[compose_hom] >>
qabbrev_tac ‘t = i₁ o to1 (R × (exp R two))’ >>
(*maybe lemma about to true_A*)
qabbrev_tac ‘ψ = eqa (ev R two) t’ >>
qabbrev_tac ‘R' = eqo (ev R two) t’ >>
‘(p1 R (exp R two))∶ (R × (exp R two)) → R ∧
 (p2 R (exp R two))∶ (R × (exp R two)) → exp R two’
 by metis_tac[p1_hom,p2_hom] >>
‘h o (p1 R (exp R two))∶ (R × (exp R two)) → A’
 by metis_tac[compose_hom] >>
‘⟨h o (p1 R (exp R two)), p2 R (exp R two)⟩∶
 (R × (exp R two)) → (A × (exp R two))’ by metis_tac[pa_hom] >>
qabbrev_tac ‘h2R = ⟨h o (p1 R (exp R two)), p2 R (exp R two)⟩’>>
‘ψ∶ R' → (R × (exp R two))’
 by
  (simp[Abbr‘ψ’,Abbr‘R'’] >> metis_tac[eqa_hom]) >>
‘h2R o ψ∶ R' → (A × (exp R two))’ by metis_tac[compose_hom] >>
drule mono_epi_fac >> strip_tac >>
drule char_thm >> strip_tac >>
first_x_assum (qspecl_then [‘X’,‘A × exp R two’] assume_tac) >>
rename [‘m∶M → (A × exp R two)’] >>
qabbrev_tac ‘ϕ = char m’ >>
‘ϕ∶A × exp R two → two’ by simp[] >>
‘ ∀x.
    x∶one → (A × exp R two) ⇒
   ((∃x0. x0∶one → M ∧ m ∘ x0 = x) ⇔ ϕ ∘ x = i₁)’
   by (simp[Abbr‘i₁’] >> metis_tac[]) >>
Q.UNDISCH_THEN `m∶M → (A × exp R two) ⇒
        ϕ∶A × exp R two → one + one ∧
        ∀x.
            x∶one → (A × exp R two) ⇒
            ((∃x0. x0∶one → M ∧ m ∘ x0 = x) ⇔ ϕ ∘ x = i2 one one)` (K ALL_TAC) >>
‘tp ϕ∶ exp R two → exp A two’ by metis_tac[tp_hom] >>
qexists_tac ‘tp ϕ’ >> simp[] >> rw[] >>
‘ev A two∶ (A × (exp A two)) → two’ by metis_tac[ev_hom] >>
‘∀r. r∶ one → R ⇒ (psi o r = i₁ ⇔
                   ∃r'. r'∶ one → R' ∧
                        ψ o r' = ⟨r, tp (psi ∘ p1 R one)⟩)’
 by (rw[] >> simp[Abbr‘R'’,Abbr‘ψ’,Abbr‘t’,Abbr‘i₁’] >>
    metis_tac[mem_of_name_eqa]) >> 
simp[EQ_IMP_THM] >> rpt strip_tac (* 2 *) 
>- (‘ϕ o ⟨x, tp (psi ∘ p1 R one)⟩ =
    ev A two ∘ ⟨p1 A one,tp ϕ ∘ tp (psi ∘ p1 R one) o p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ x’ by metis_tac[compose_partial_ev] >> 
   (*need lemma*)
   (*use fact that epi has section*)
   ‘ϕ o ⟨x, tp (psi ∘ p1 R one)⟩ = i₁’ by metis_tac[] >>
   drule fac_char_via_any_map >> strip_tac >>
   first_x_assum (qspecl_then [‘h2R o ψ’,‘R'’,‘A × (exp R two)’,
                               ‘M’,‘m’,
                               ‘⟨x,tp (psi o p1 R one)⟩’]
                  assume_tac) >>
   ‘(psi ∘ p1 R one)∶ (R × one) → two’
    by metis_tac[compose_hom,p1_hom] >>
   ‘tp (psi ∘ p1 R one)∶ one → exp R two’
    by metis_tac[tp_hom] >>
   ‘⟨x,tp (psi ∘ p1 R one)⟩∶one → (A × exp R two)’
    by metis_tac[pa_hom] >> 
   ‘∃r'. r'∶one → R' ∧ (h2R ∘ ψ) ∘ r' = ⟨x,tp (psi ∘ p1 R one)⟩’
     by (first_x_assum irule >>
        metis_tac[Abbr‘ϕ’,Abbr‘i₁’]) >> 
   ‘(p1 R (exp R two)) o ψ o r'∶ one → R’
    by metis_tac[compose_hom] >>
   qexists_tac ‘(p1 R (exp R two)) o ψ o r'’ >>
   simp[] >> 
   rw[] (* 2 *)
   >- (qexists_tac ‘r'’ >> simp[] >>
      ‘psi o (p1 R one)∶ (R × one) → two’
       by metis_tac[compose_hom,p1_hom] >>
      ‘tp (psi ∘ p1 R one)∶ one → exp R two’
        by metis_tac[tp_hom] >>
      ‘p2 R (exp R two) o ψ ∘ r' =
       tp (psi ∘ p1 R one)’
      suffices_by
       (rw[] >> irule to_p_eq_applied >>
       ‘ψ o r'∶ one → (R × exp R two)’
        by metis_tac[compose_hom] >>
       ‘⟨p1 R (exp R two) ∘ ψ ∘ r',tp (psi ∘ p1 R one)⟩∶
        one → (R × exp R two)’
        by metis_tac[pa_hom] >> 
       qexistsl_tac [‘R’,‘exp R two’,‘one’] >>
       simp[] >>
       ‘tp (psi ∘ p1 R one) =
        p2 R (exp R two) ∘ ⟨p1 R (exp R two) ∘ ψ ∘ r',tp (psi ∘ p1 R one)⟩’ by metis_tac[p2_of_pa] >>
       simp[] >>
       metis_tac[p1_of_pa]) >>
      ‘p2 A (exp R two) o (h2R ∘ ψ) ∘ r' =
       p2 A (exp R two) o ⟨x,tp (psi ∘ p1 R one)⟩’
       by metis_tac[] >>
      ‘p2 A (exp R two) o ⟨x,tp (psi ∘ p1 R one)⟩ =
       tp (psi ∘ p1 R one)’ by metis_tac[p2_of_pa] >>
      ‘p2 R (exp R two) = p2 A (exp R two) o h2R’
        by (simp[Abbr‘h2R’] >> metis_tac[p2_of_pa]) >>
      simp[] >>
      ‘(p2 A (exp R two) ∘ h2R) ∘ ψ ∘ r' =
       p2 A (exp R two) ∘ (h2R ∘ ψ) ∘ r'’
       suffices_by metis_tac[] >>
      irule compose_assoc_4_2_left_middle >>
            metis_tac[p2_hom])
   >- (‘p1 A (exp R two) o  (h2R ∘ ψ) ∘ r' = x’
        by (simp[] >> metis_tac[p1_of_pa]) >>
      ‘p1 A (exp R two) ∘ h2R = h ∘ p1 R (exp R two)’
       by (simp[Abbr‘h2R’] >> metis_tac[p1_of_pa]) >>
      ‘p1 A (exp R two) ∘ (h2R ∘ ψ) ∘ r' =
       (p1 A (exp R two) ∘ h2R) ∘ ψ ∘ r'’
       by metis_tac[compose_assoc_4_2_left_middle,p1_hom] >>
      ‘(p1 A (exp R two) ∘ h2R) ∘ ψ ∘ r' = x’
       by metis_tac[] >>
      ‘(h ∘ p1 R (exp R two)) ∘ ψ ∘ r' = x’
       by metis_tac[] >>
      metis_tac[compose_assoc_4_2_left,p1_hom]))
>- (‘ev A two ∘ ⟨p1 A one,tp ϕ ∘ tp (psi ∘ p1 R one) o p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ x = ϕ o ⟨x, tp (psi ∘ p1 R one)⟩’ by
    metis_tac[compose_partial_ev] >>
   simp[SimpLHS] >>
   ‘∃r'. r'∶one → R' ∧ ψ ∘ r' = ⟨r, tp (psi ∘ p1 R one)⟩’
    by metis_tac[] >>
   Q.UNDISCH_THEN
   ‘∀r.  r∶one → R ⇒
            (psi ∘ r = i₁ ⇔
             ∃r'. r'∶one → R' ∧ ψ ∘ r' = ⟨r,tp (psi ∘ p1 R one)⟩)’ (K ALL_TAC) >>
   ‘(h2R o ψ) ∘ r' = h2R o ⟨r, tp (psi ∘ p1 R one)⟩’
    by metis_tac[compose_assoc] >>
   ‘m o e o r' = h2R ∘ ⟨r, tp (psi ∘ p1 R one)⟩’
    by metis_tac[compose_assoc] >>
   ‘(psi ∘ p1 R one)∶ (R × one) → two’
    by metis_tac[compose_hom,p1_hom] >>
   ‘tp (psi ∘ p1 R one)∶ one → exp R two’
    by metis_tac[tp_hom] >>
   ‘⟨x,tp (psi ∘ p1 R one)⟩∶one → (A × exp R two)’
    by metis_tac[pa_hom] >> 
   ‘h2R ∘ ⟨r,tp (psi ∘ p1 R one)⟩ =⟨x, tp (psi ∘ p1 R one)⟩’
    by
     (irule to_p_eq_applied >>
     qexistsl_tac [‘A’,‘exp R two’,‘one’] >>
     simp[] >>
     ‘⟨r,tp (psi ∘ p1 R one)⟩∶ one → (R × exp R two)’
      by metis_tac[pa_hom] >>
     ‘h2R ∘ ⟨r,tp (psi ∘ p1 R one)⟩∶one → (A × exp R two)’
      by metis_tac[compose_hom] >>
     simp[] >>
     simp[Abbr‘h2R’] >>
     ‘p2 A (exp R two) ∘ ⟨x,tp (psi ∘ p1 R one)⟩ =
      tp (psi ∘ p1 R one)’ by metis_tac[p2_of_pa] >>
     ‘p1 A (exp R two) ∘ ⟨x,tp (psi ∘ p1 R one)⟩ = x’
      by metis_tac[p1_of_pa] >>
     simp[] >>
     ‘⟨h ∘ p1 R (exp R two),p2 R (exp R two)⟩∶
      (R × (exp R two)) → (A × (exp R two))’
      by metis_tac[compose_hom,pa_hom] >>
     ‘p1 A (exp R two) ∘ ⟨h ∘ p1 R (exp R two),p2 R (exp R two)⟩ ∘ ⟨r,tp (psi ∘ p1 R one)⟩ =
      (p1 A (exp R two) ∘ ⟨h ∘ p1 R (exp R two),p2 R (exp R two)⟩) ∘ ⟨r,tp (psi ∘ p1 R one)⟩’
      by metis_tac[p1_hom,compose_assoc] >>
     ‘p2 A (exp R two) ∘ ⟨h ∘ p1 R (exp R two),p2 R (exp R two)⟩ ∘ ⟨r,tp (psi ∘ p1 R one)⟩ =
      (p2 A (exp R two) ∘ ⟨h ∘ p1 R (exp R two),p2 R (exp R two)⟩) ∘ ⟨r,tp (psi ∘ p1 R one)⟩’
      by metis_tac[p2_hom,compose_assoc] >>
     simp[] >>
     ‘p1 A (exp R two) ∘ ⟨h ∘ p1 R (exp R two),p2 R (exp R two)⟩ = h ∘ p1 R (exp R two)’ by metis_tac[compose_hom,p1_of_pa] >>
     ‘p2 A (exp R two) ∘ ⟨h ∘ p1 R (exp R two),p2 R (exp R two)⟩ = p2 R (exp R two)’ by metis_tac[compose_hom,p2_of_pa] >>
     simp[] >>
     ‘p2 R (exp R two) ∘ ⟨r,tp (psi ∘ p1 R one)⟩ =
      tp (psi ∘ p1 R one)’ by metis_tac[p2_of_pa] >>
     simp[] >>
     ‘(h ∘ p1 R (exp R two)) ∘ ⟨r,tp (psi ∘ p1 R one)⟩ =
      h ∘ p1 R (exp R two) ∘ ⟨r,tp (psi ∘ p1 R one)⟩’
      by metis_tac[compose_assoc] >>
     simp[] >>
     ‘p1 R (exp R two) ∘ ⟨r,tp (psi ∘ p1 R one)⟩ = r’
      by metis_tac[p1_of_pa] >>
     metis_tac[]) >>
   ‘ϕ ∘ h2R ∘ ⟨r,tp (psi ∘ p1 R one)⟩ = i₁’
    by (simp[Abbr‘ϕ’,Abbr‘i₁’] >>
       drule fac_char >> strip_tac >>
       first_x_assum (qspecl_then [‘M’,‘(A × exp R two)’,‘one’,‘⟨x,tp (psi ∘ p1 R one)⟩’,‘e o r'’] assume_tac) >>
       ‘to1 one = id one’ by metis_tac[to1_unique,id1,to1_hom]>>
       ‘i2 one one = i2 one one o id one’
        by metis_tac[idR] >>
       ‘char m ∘ ⟨x,tp (psi ∘ p1 R one)⟩ = i2 one one o to1 one’
        suffices_by metis_tac[] >>
       first_x_assum irule >> rw[] >>
       metis_tac[compose_hom,pa_hom]) >>
       metis_tac[])
(*
     cheat >>
   ‘h2R ∘ ⟨r,tp (psi ∘ p2 one R)⟩ = ⟨x,tp (psi ∘ p2 one R)⟩’
    by cheat >>
   metis_tac[]
   (*use fac_char*)*)
  
QED


Theorem bar_exists:
∀h.  ∃hb. hb∶ exp (dom h) (one + one) → exp (cod h) (one + one) ∧
             (∀psi. psi∶ (dom h) → one + one ⇒
                    ∀x. x∶ one → (cod h) ⇒
                        (ev (cod h) (one + one) o ⟨p1 (cod h) one, hb o tp (psi o p1 (dom h) one) o p2 (cod h) one⟩ o ⟨id (cod h), to1 (cod h)⟩ o x = i2 one one ⇔
                         ∃r. r∶ one → (dom h) ∧
                             psi o r = i2 one one ∧
                             h o r = x))
Proof
rw[] >>
qabbrev_tac ‘R = dom h’ >>
qabbrev_tac ‘A = cod h’ >>
‘h∶ R → A’ by metis_tac[hom_def] >>
drule Thm6_lemma_3 >> rw[]
QED   


Theorem diag_is_mono:
∀A. is_mono ⟨id A,id A⟩
Proof
rw[] >> ‘⟨id A,id A⟩∶ A → (A × A)’ by metis_tac[id1,pa_hom] >>
irule is_mono_applied >> qexistsl_tac [‘A’,‘A × A’] >> rw[] >>
‘p1 A A o ⟨id A,id A⟩ ∘ f = p1 A A o ⟨id A,id A⟩ ∘ g’
 by metis_tac[] >>
‘p1 A A ∘ ⟨id A,id A⟩ ∘ f =  (p1 A A ∘ ⟨id A,id A⟩) ∘ f ∧
 p1 A A ∘ ⟨id A,id A⟩ ∘ g =  (p1 A A ∘ ⟨id A,id A⟩) ∘ g’
 by metis_tac[p1_hom,compose_assoc] >>
metis_tac[p1_of_pa,idL,id1]
QED

Theorem fac_diag_eq:
∀x0 x y A. x∶ one → A ∧ y∶ one → A ∧ x0∶ one → A ∧
         ⟨id A,id A⟩ ∘ x0 = ⟨y,x⟩ ⇒
         y = x
Proof
rw[] >>
‘p1 A A∶ (A × A) → A ∧ p2 A A∶ (A × A) → A’
 by metis_tac[p1_hom,p2_hom] >>
‘⟨id A,id A⟩∶ A → (A × A)’ by metis_tac[id1,pa_hom] >>
‘p1 A A o ⟨id A,id A⟩ ∘ x0 = p1 A A o ⟨y,x⟩ ∧
 p2 A A o ⟨id A,id A⟩ ∘ x0 = p2 A A o ⟨y,x⟩’ by metis_tac[] >>
‘p1 A A o ⟨y,x⟩ = y ∧ p2 A A o ⟨y,x⟩ = x’
 by metis_tac[p1_of_pa,p2_of_pa] >>
simp[] >>
‘p1 A A ∘ ⟨id A,id A⟩ ∘ x0 =
 p2 A A ∘ ⟨id A,id A⟩ ∘ x0’ suffices_by metis_tac[] >>
‘p1 A A ∘ ⟨id A,id A⟩ =
 p2 A A ∘ ⟨id A,id A⟩’ suffices_by metis_tac[compose_assoc] >>
metis_tac[id1,p1_of_pa,p2_of_pa]
QED        
                 


Theorem Thm6_lemma_2:
∀A. ∃sg. sg∶ A → exp A (one + one) ∧
    ∀x y. x∶ one → A ∧ y∶ one → A ⇒
          (ev A (one + one) o ⟨p1 A one, sg o x o p2 A one⟩ o ⟨id A, to1 A⟩ o y =
           i2 one one ⇔ y = x)
Proof
rw[] >>
qexists_tac ‘tp (char ⟨id A,id A⟩)’ >>
‘is_mono ⟨id A,id A⟩’ by metis_tac[diag_is_mono] >>
drule char_thm >> strip_tac >>
‘⟨id A,id A⟩∶ A → (A × A)’ by metis_tac[id1,pa_hom] >>
first_x_assum drule >> strip_tac >>
‘tp (char ⟨id A,id A⟩)∶A → exp A (one + one)’
 by metis_tac[tp_hom] >>
simp[] >> rw[] >>
‘⟨p1 A one,tp (char ⟨id A,id A⟩) ∘ x o p2 A one⟩ =
 ⟨p1 A A,tp (char ⟨id A,id A⟩) o p2 A A⟩ o ⟨p1 A one, x o p2 A one⟩’
 by (irule parallel_p_one_side >> metis_tac[]) >>
rw[] >>
‘⟨p1 A one,x ∘ p2 A one⟩∶ (A × one) → (A × A)’
 by metis_tac[compose_hom,p1_hom,p2_hom,pa_hom] >>
‘⟨id A,to1 A⟩∶ A → (A × one)’ by metis_tac[id1,to1_hom,pa_hom]>>
‘ev A (one + one) ∶ (A × (exp A (one + one))) → (one+ one)’
 by metis_tac[ev_hom] >>
‘⟨p1 A A,tp (char ⟨id A,id A⟩) ∘ p2 A A⟩∶
 (A × A) → (A × (exp A (one + one)))’
 by metis_tac[p1_hom,p2_hom,compose_hom,pa_hom]>>
‘ev A (one + one) ∘
        (⟨p1 A A,tp (char ⟨id A,id A⟩) ∘ p2 A A⟩ ∘ ⟨p1 A one,x ∘ p2 A one⟩) ∘
        ⟨id A,to1 A⟩ ∘ y =
 (ev A (one + one) ∘
        ⟨p1 A A,tp (char ⟨id A,id A⟩) ∘ p2 A A⟩) ∘ ⟨p1 A one,x ∘ p2 A one⟩ ∘
        ⟨id A,to1 A⟩ ∘ y’
 by metis_tac[compose_assoc_5_2_left1_left] >>
rw[] >>
‘(ev A (one + one) ∘ ⟨p1 A A,tp (char ⟨id A,id A⟩) ∘ p2 A A⟩) =
 char ⟨id A,id A⟩’
 by metis_tac[ev_of_tp] >>
rw[] >>
‘⟨y,x⟩∶ one → (A × A)’ by metis_tac[pa_hom] >>
‘⟨p1 A one,x ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ y∶ one → (A × A)’
 by metis_tac[compose_hom] >>
‘⟨p1 A one,x ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ y =
 ⟨y,x⟩’
 by  (drule to_p_eq_applied >> rw[] >> first_x_assum irule >>
     simp[] >>
     ‘(p1 A A) o ⟨y,x⟩ = y ∧ (p2 A A) o ⟨y,x⟩ = x’
      by metis_tac[p1_of_pa,p2_of_pa] >>
     simp[] >>
     ‘p1 A A ∘ ⟨p1 A one,x ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ y =
      (p1 A A ∘ ⟨p1 A one,x ∘ p2 A one⟩) ∘ ⟨id A,to1 A⟩ ∘ y ∧
      p2 A A ∘ ⟨p1 A one,x ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ y =
      (p2 A A ∘ ⟨p1 A one,x ∘ p2 A one⟩) ∘ ⟨id A,to1 A⟩ ∘ y’
      by metis_tac[p1_hom,p2_hom,compose_assoc_4_2_left] >>
     simp[] >>
     ‘(p1 A A ∘ ⟨p1 A one,x ∘ p2 A one⟩) = p1 A one ∧
      (p2 A A ∘ ⟨p1 A one,x ∘ p2 A one⟩) = x o p2 A one’
      by metis_tac[compose_hom,p1_hom,p2_hom,
                   p1_of_pa,p2_of_pa]>>
     simp[] >>
     ‘p1 A one o ⟨id A, to1 A⟩ o y =
      (p1 A one o ⟨id A, to1 A⟩) o y ∧
     (x ∘ p2 A one) ∘ ⟨id A,to1 A⟩ ∘ y =
     ((x ∘ p2 A one) ∘ ⟨id A,to1 A⟩) ∘ y’
      by metis_tac[compose_hom,compose_assoc,p1_hom,p2_hom] >>
     simp[] >>
     ‘p1 A one o ⟨id A, to1 A⟩ = id A’
      by metis_tac[p1_of_pa,id1,to1_hom] >>
     ‘(x ∘ p2 A one) ∘ ⟨id A,to1 A⟩ =
      x ∘ p2 A one ∘ ⟨id A,to1 A⟩’
      by metis_tac[p2_hom,compose_assoc,id1,to1_hom,pa_hom] >>
     simp[] >>
     ‘p2 A one ∘ ⟨id A,to1 A⟩ = to1 A’
      by metis_tac[p2_hom,id1,to1_hom,p2_of_pa] >>
     simp[] >> 
     ‘(x ∘ to1 A) ∘ y = x ∘ to1 A ∘ y’
      by metis_tac[to1_hom,compose_assoc] >>
     ‘to1 A o y = id one’
      by (irule to1_unique >>
         metis_tac[compose_hom,to1_hom,id1]) >>
     simp[] >>
     metis_tac[idL,idR]) >>
simp[] >> first_x_assum (qspec_then ‘⟨y,x⟩’ assume_tac) >>
first_x_assum drule >> rw[] >>
‘(∃x0. x0∶one → A ∧ ⟨id A,id A⟩ ∘ x0 = ⟨y,x⟩) ⇔ y = x’
 suffices_by metis_tac[] >>
Q.UNDISCH_THEN
  ‘(∃x0. x0∶one → A ∧ ⟨id A,id A⟩ ∘ x0 = ⟨y,x⟩) ⇔
   char ⟨id A,id A⟩ ∘ ⟨y,x⟩ = i2 one one’ (K ALL_TAC) >>
simp[] >>
rw[EQ_IMP_THM]
>- metis_tac[fac_diag_eq] >>
qexists_tac ‘x’ >> rw[] >>
drule to_p_eq_applied >> rw[] >>
‘⟨x,x⟩ = ⟨id A,id A⟩ ∘ x’
 suffices_by metis_tac[] >>
first_x_assum irule >> rw[] (* 3 *)
>- (‘p1 A A ∘ ⟨id A,id A⟩ ∘ x = (p1 A A ∘ ⟨id A,id A⟩) ∘ x’
     by metis_tac[compose_assoc,p1_hom] >>
   simp[] >> metis_tac[p1_of_pa,idL,id1])
>- metis_tac[p2_of_pa,idL,id1,compose_assoc,p2_hom]
>- metis_tac[compose_hom]
QED



Theorem sg_exists_thm = SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] Thm6_lemma_2        

val sg_def = new_specification ("sg_def",["sg"],sg_exists_thm)        


Theorem bar_exists_thm = SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] bar_exists  

val bar_def = new_specification ("bar_def",["bar"],bar_exists_thm)


Theorem bar_thm:
∀h R A. h∶ R → A ⇒
         bar h∶exp R two → exp A two ∧
         ∀psi.
             psi∶ R → two ⇒
             ∀x.
                 x∶one → A ⇒
                 (ev A two ∘
                  ⟨p1 A one,bar h ∘ tp (psi ∘ p1 R one) ∘
                  p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ x =
                  i2 one one ⇔
                  ∃r. r∶one → R ∧ psi ∘ r = i2 one one ∧ h ∘ r = x)
Proof
strip_tac >> strip_tac >> strip_tac >> strip_tac >>
‘dom h = R ∧ cod h = A’ by metis_tac[hom_def] >>
metis_tac[bar_def]
QED



Theorem Thm6_g_ev_psi:
!R A s0 a f0. a∶ one → A ∧ s0∶ A →  exp A two ∧ f0∶ R → A ==>
ev A two ∘ ⟨p1 A one,s0 ∘ a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ f0 ∘ p1 R one =
 ev R two o ⟨p1 R one, tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ s0 ∘ a ∘ p2 R one⟩
Proof
rw[] >>
‘ev R two ∘
 ⟨p1 R one,tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ s0 ∘ a ∘ p2 R one⟩’
        
        
Theorem Thm6_g_ev:
∀a a' f0 f1 R A.
 a∶ one → A ∧ a'∶ one → A ∧ f0∶ R → A ∧ f1∶ R → A ⇒
 (ev A two o
 ⟨p1 A one,
  bar f1 o
  (tp (ev A two o ⟨f0 o p1 R (exp A two),p2 R (exp A two)⟩)) o
  sg A o a o p2 A one⟩ o ⟨id A,to1 A⟩ o
 a' = i2 one one ⇔
 (∃r. r∶ one → R ∧ f0 o r = a ∧ f1 o r = a'))
Proof 
rw[] >> drule bar_thm >> rw[] >>
(*needed*)
‘ev A two ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ f0 ∶ R → two’ by cheat >>
‘ev A two ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ f0 ∘ p1 R one =
 ev R two o ⟨p1 R one, tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘ a ∘ p2 R one⟩ ’

     
‘∃psi. psi∶ R → two ∧
       tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘ a = tp (psi ∘ p1 R one) ’ by cheat >>
simp[] >>
‘bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘ a ∘
        p2 A one =
 bar f1 ∘
        (tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘ a) ∘
        p2 A one’ by cheat >> simp[] >>
‘∀r. r∶ one → R ⇒ (f0 o r = a ⇔ psi o r = i2 one one)’
 suffices_by metis_tac[] >>
rw[] >>
‘psi = ev A two ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ f0’ by cheat (*need a lemma about psi*)>>
simp[] >>
‘(ev A two ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ f0 o r =
              i2 one one ⇔ f0 o r = a)’
 by (irule (sg_def |> SPEC_ALL |> CONJUNCT2) >>
    metis_tac[compose_hom]) >>
‘ev A two ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ f0 ∘ r =
 (ev A two ∘ ⟨p1 A one,sg A ∘ a ∘ p2 A one⟩ ∘ ⟨id A,to1 A⟩ ∘ f0) ∘ r’ suffices_by metis_tac[] >>
irule compose_assoc_5_4_left >>
cheat
(*smart way for such matching?*)
QED

Theorem Thm6_g_ev':
∀a a' f0 f1 R A.
         a∶one → A ∧ a'∶one → A ∧ f0∶R → A ∧ f1∶R → A ⇒
         (ev A two ∘
          ⟨p1 A one,bar f1 ∘
          tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
          a ∘ p2 A one⟩ ∘ ⟨a',id one⟩ =
          i2 one one ⇔ ∃r. r∶one → R ∧ f0 ∘ r = a ∧ f1 ∘ r = a')
Proof
cheat
QED


Theorem is_trans_thm:
∀f0 f1 R A. f0∶ R → A ∧ f1∶ R → A ⇒
         (is_trans f0 f1 ⇔
         ∀X h0 h1.
             h0∶X → R ∧ h1∶X → R ∧ f1 ∘ h0 = f0 ∘ h1 ⇒
             ∃u. u∶X → R ∧ f0 ∘ u = f0 ∘ h0 ∧ f1 ∘ u = f1 ∘ h1)
Proof
rw[] >>
metis_tac[is_trans_def,hom_def]
QED
(*

Theorem is_trans_thm':
∀f0 f1 R A. f0∶ R → A ∧ f1∶ R → A ⇒
         (is_trans f0 f1 ⇒
         ∀X h0 h1.
             h0∶X → R ∧ h1∶X → R ∧ f1 ∘ h0 = f0 ∘ h1 ⇒
             ∃u. u∶X → R ∧ f0 ∘ u = f0 ∘ h0 ∧ f1 ∘ u = f1 ∘ h1)
Proof
metis_tac[is_trans_thm]
QED
 
*)
Theorem symm_trans_rel_lemma:
∀f0 f1 a R A r.
 is_symm f0 f1 ∧ is_trans f0 f1 ∧
 f0∶ R → A ∧ f1∶ R → A ∧ a∶ one → A ∧ r∶ one → R ⇒
       ((∃r'. r'∶one → R ∧ f0 ∘ r' = f0 ∘ r ∧ f1 ∘ r' = a) ⇔
        (∃r''. r''∶one → R ∧ f0 ∘ r'' = f1 ∘ r ∧ f1 ∘ r'' = a))
Proof
rw[EQ_IMP_THM] (* 2 *)
>- (‘∃t. t∶ R → R ∧ f0 o t = f1 ∧ f1 o t = f0’
     by metis_tac[is_symm_def,hom_def] >>
   ‘f1 o t ∘ r' = f0 ∘ r’
    by metis_tac[compose_assoc] >>
   ‘(is_trans f0 f1 ⇔
          ∀X h0 h1.
              h0∶X → R ∧ h1∶X → R ∧ f1 ∘ h0 = f0 ∘ h1 ⇒
              ∃u. u∶X → R ∧ f0 ∘ u = f0 ∘ h0 ∧ f1 ∘ u = f1 ∘ h1)’ by (irule is_trans_thm >> metis_tac[]) >>  rfs[] >>
   ‘t o r'∶ one → R’ by metis_tac[compose_hom] >>
  first_x_assum (qspecl_then [‘one’,‘t o r'’,‘r’] assume_tac)>>
  ‘∃u. u∶one → R ∧ f0 ∘ u = f0 ∘ t ∘ r' ∧ f1 ∘ u = f1 ∘ r’
   by metis_tac[] >>
  qexists_tac ‘t o u’ >>
  ‘t o u∶ one → R’ by metis_tac[compose_hom] >>
  metis_tac[compose_assoc])
>- (‘(is_trans f0 f1 ⇔
          ∀X h0 h1.
              h0∶X → R ∧ h1∶X → R ∧ f1 ∘ h0 = f0 ∘ h1 ⇒
              ∃u. u∶X → R ∧ f0 ∘ u = f0 ∘ h0 ∧ f1 ∘ u = f1 ∘ h1)’ by (irule is_trans_thm >> metis_tac[]) >>  rfs[])
QED              
  
              


        
Theorem to_p_with_1:
∀A a. a∶ one → (A × one) ⇒ ∃a0. a0∶one → A ∧
      a = ⟨a0, id one⟩
Proof
rw[] >> qexists_tac ‘p1 A one o a’ >>
‘p1 A one o a∶ one → A’ by metis_tac[compose_hom,p1_hom] >>
‘⟨p1 A one o a, id one⟩∶ one → (A × one)’ by metis_tac[id1,pa_hom] >>
rw[] >> irule to_p_eq_applied >> qexistsl_tac [‘A’,‘one’,‘one’] >>
simp[] >>
‘p2 A one o a∶ one → one’ by metis_tac[p2_hom,compose_hom] >>
‘p2 A one o a = id one’ by metis_tac[id1,to1_unique] >>
‘p2 A one ∘ ⟨p1 A one ∘ a,id one⟩ = id one’
 by metis_tac[p2_of_pa,id1] >>
simp[] >>
metis_tac[id1,p1_of_pa]
QED

Theorem one_to_two_cases:
∀f. f∶ one → two ⇒ f = i1 one one ∨ f = i2 one one
Proof
rw[] >> drule to_copa_fac >> rw[] (* 2 *)
>- (‘x0 = id one’ by metis_tac[id1,to1_unique] >> simp[] >>
   metis_tac[i1_hom,idR]) >>
‘x0' = id one’ by metis_tac[id1,to1_unique] >> simp[] >>
metis_tac[i2_hom,idR] 
QED
   
Theorem one_to_two_eq:
∀f g. f∶ one → two ∧ g∶ one → two ∧
      (f = i2 one one ⇔ g = i2 one one) ⇒ f = g
Proof
rw[] >> Cases_on ‘f = i2 one one’
>- metis_tac[]
>- (‘g ≠ i2 one one’ by metis_tac[] >>
   metis_tac[one_to_two_cases])
QED
        
        
Theorem f0g_eq_f1g:
∀f0 f1 R A.
 f0∶ R → A ∧ f1∶ R → A ∧ is_symm f0 f1 ∧ is_trans f0 f1 ⇒
 (bar f1 o
  (tp (ev A two o ⟨f0 o p1 R (exp A two),p2 R (exp A two)⟩)) o
  sg A) o f0 =
 (bar f1 o
  (tp (ev A two o ⟨f0 o p1 R (exp A two),p2 R (exp A two)⟩)) o
  sg A) o f1
Proof
rw[] >> 
irule fun_ext >>
qexistsl_tac [‘R’,‘exp A two’] >>
‘(bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
         sg A) ∘ f0∶R →
        exp A two ∧
        (bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
         sg A) ∘ f1∶R →
        exp A two’ by cheat >>
simp[] >> rw[] >>
rename [‘r∶ one → R’] >>
‘((bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
          sg A) ∘ f0) ∘ r∶ one → exp A two ∧
 ((bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
          sg A) ∘ f1) ∘ r∶ one → exp A two’
 by cheat >>
irule ev_eq_eq >>
qexistsl_tac [‘A’,‘two’,‘one’] >> simp[] >>
‘ev A two ∘
        ⟨p1 A one,(((bar f1 ∘
           tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A) ∘
          f0) ∘ r) ∘ p2 A one⟩∶ (A × one) → two ∧
 ev A two ∘
        ⟨p1 A one,(((bar f1 ∘
           tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A) ∘
          f1) ∘ r) ∘ p2 A one⟩∶ (A × one) → two’
 by cheat >> irule fun_ext >>
qexistsl_tac [‘A × one’,‘two’] >> simp[] >>
rw[] >>
‘∃a0. a0∶ one → A ∧ a = ⟨a0, id one⟩’
 by metis_tac[to_p_with_1]>>
simp[] >>
‘(ev A two ∘
         ⟨p1 A one,(((bar f1 ∘
            tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A) ∘
           f0) ∘ r) ∘ p2 A one⟩) ∘ ⟨a0,id one⟩ =
ev A two ∘
         ⟨p1 A one,bar f1 ∘
            tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
           (f0 ∘ r) ∘ p2 A one⟩ ∘ ⟨a0,id one⟩’ by cheat >>
‘(ev A two ∘
         ⟨p1 A one,(((bar f1 ∘
            tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A) ∘
           f1) ∘ r) ∘ p2 A one⟩) ∘ ⟨a0,id one⟩ =
ev A two ∘
         ⟨p1 A one,bar f1 ∘
            tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
           (f1 ∘ r) ∘ p2 A one⟩ ∘ ⟨a0,id one⟩’ by cheat >>
simp[] >>
‘f0 o r∶ one → A’ by metis_tac[compose_hom] >>
drule Thm6_g_ev' >> strip_tac >>
first_x_assum (qspecl_then [‘a0’,‘f0’,‘f1’,‘R’] assume_tac) >>
first_x_assum drule_all >> rw[] >>
‘f1 o r∶ one → A’ by metis_tac[compose_hom] >>
drule Thm6_g_ev' >> strip_tac >>
first_x_assum (qspecl_then [‘a0’,‘f0’,‘f1’,‘R’] assume_tac) >>
first_x_assum drule_all >> rw[] >>
‘ev A two ∘
              ⟨p1 A one,bar f1 ∘
              tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
              sg A ∘ (f0 ∘ r) ∘ p2 A one⟩ ∘ ⟨a0,id one⟩∶ one → two’ by cheat >>
‘ev A two ∘
         ⟨p1 A one,bar f1 ∘
         tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
         (f1 ∘ r) ∘ p2 A one⟩ ∘ ⟨a0,id one⟩∶ one → two’
 by cheat  >>
irule one_to_two_eq >> simp[] >> rw[] >>
drule symm_trans_rel_lemma >> strip_tac >>
first_x_assum (qspecl_then [‘a0’,‘R’,‘A’,‘r’] assume_tac) >>
metis_tac[]
QED

Theorem Thm6_page29_means_just_that:
∀f0 f1 R A a0 a1.
         f0∶R → A ∧ f1∶R → A  ∧
         a0∶ one → A ∧ a1∶ one → A ∧
bar f1 o
  (tp (ev A two o ⟨f0 o p1 R (exp A two),p2 R (exp A two)⟩)) o
  sg A o a0 =
bar f1 o
  (tp (ev A two o ⟨f0 o p1 R (exp A two),p2 R (exp A two)⟩)) o
  sg A o a1 ⇒
∀a'. a'∶ one → A ⇒
    ((∃r. r∶one → R ∧ f0 ∘ r = a0 ∧ f1 ∘ r = a') ⇔
     (∃r. r∶one → R ∧ f0 ∘ r = a1 ∧ f1 ∘ r = a'))
Proof
rw[] >>
‘ev A two ∘
 ⟨p1 A one,bar f1 ∘
  tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘  a0 ∘ p2 A one⟩ ∘ ⟨a',id one⟩ = i2 one one ⇔
  ∃r. r∶one → R ∧ f0 ∘ r = a0 ∧ f1 ∘ r = a'’
  by (irule Thm6_g_ev' >> rw[]) >>
‘ev A two ∘
 ⟨p1 A one,bar f1 ∘
  tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘  a1 ∘ p2 A one⟩ ∘ ⟨a',id one⟩ = i2 one one ⇔
  ∃r. r∶one → R ∧ f0 ∘ r = a1 ∧ f1 ∘ r = a'’
  by (irule Thm6_g_ev' >> rw[]) >>
‘ev A two ∘
 ⟨p1 A one,bar f1 ∘
           tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘ a0 ∘ p2 A one⟩ ∘ ⟨a',id one⟩ =
 ev A two ∘
 ⟨p1 A one,bar f1 ∘
           tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘ a1 ∘ p2 A one⟩ ∘ ⟨a',id one⟩’
  suffices_by metis_tac[] >>
Q.UNDISCH_THEN
‘ev A two ∘
 ⟨p1 A one,bar f1 ∘
           tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a0 ∘ p2 A one⟩ ∘ ⟨a',id one⟩ =
        i2 one one ⇔ ∃r. r∶one → R ∧ f0 ∘ r = a0 ∧ f1 ∘ r = a'’
 (K ALL_TAC) >>
Q.UNDISCH_THEN
‘ev A two ∘
        ⟨p1 A one,bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a1 ∘ p2 A one⟩ ∘ ⟨a',id one⟩ =
        i2 one one ⇔ ∃r. r∶one → R ∧ f0 ∘ r = a1 ∧ f1 ∘ r = a'’
 (K ALL_TAC) >>
qabbrev_tac ‘l1 = bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘ a0’ >>
qabbrev_tac ‘l2 = bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘ a1’ >>
‘l1∶ one → exp A two ∧ l2∶ one → exp A two’
 by cheat >> 
‘ev A two o ⟨p1 A one, l1 o p2 A one⟩ =
 ev A two o ⟨p1 A one, l2 o p2 A one⟩’
 by metis_tac[] >>
‘ev A two ∘
        ⟨p1 A one,bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a0 ∘ p2 A one⟩ =
 ev A two ∘
        ⟨p1 A one,bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a1 ∘ p2 A one⟩’ suffices_by cheat >> 
qpat_x_assum ‘_ = _’ mp_tac >> fs[Abbr‘l1’,Abbr‘l2’] >>
‘(bar f1 ∘
         tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
         a0) ∘ p2 A one =
 bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a0 ∘ p2 A one ∧
 (bar f1 ∘
         tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
         a1) ∘ p2 A one =
 bar f1 ∘
        tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A ∘
        a1 ∘ p2 A one’  suffices_by metis_tac[] >>
cheat
(* assoc again... *)
QED

(*confused when should I use metis and irule...*)

Theorem is_refl_thm:
∀f0 f1 R A. f0∶ R → A ∧ f1∶ R → A ⇒
         (is_refl f0 f1 ⇔
         ∃d. d∶ A → R ∧ f0 ∘ d = id A ∧ f1 ∘ d = id A)
Proof
rw[] >>
metis_tac[is_refl_def,hom_def]
QED

val is_refl_thm_l2r =
      is_refl_thm
      |> SPEC_ALL |> SPEC_ALL |> SPEC_ALL |> SPEC_ALL
      |> UNDISCH |> EQ_IMP_RULE |> #1 |> UNDISCH
      |> DISCH “f0∶R → A ∧ f1∶R → A” |> DISCH_ALL
      |> Q.GEN ‘R’ |> Q.GEN ‘A’ |> Q.GEN ‘f0’ |> Q.GEN ‘f1’  
            
Theorem is_refl_equiv_to_itself:
∀f0 f1 a A R.
 is_refl f0 f1 ∧ f0∶ R → A ∧ f1∶ R → A ∧ a∶ one → A ⇒
 ∃r. r∶ one → R ∧ f0 o r = a ∧ f1 o r = a
Proof
rw[] >> drule is_refl_thm_l2r >> rw[] >>
first_x_assum drule_all >> rw[] >>
qexists_tac ‘d o a’ >>
‘d o a∶ one → R’ by metis_tac[compose_hom] >>
metis_tac[compose_assoc,idL]
QED

        
Theorem equiv_to_same_element:
∀a0 a1 f0 f1 R A.
 a0∶ one → A ∧ a1∶ one → A ∧ f0∶ R → A ∧ f1∶ R → A ∧
 is_refl f0 f1 ∧
  (∀a'.
             a'∶one → A ⇒
             ((∃r. r∶one → R ∧ f0 ∘ r = a0 ∧ f1 ∘ r = a') ⇔
              ∃r. r∶one → R ∧ f0 ∘ r = a1 ∧ f1 ∘ r = a')) ⇒
  ∃r. r∶ one → R ∧ f0 o r = a0 ∧ f1 o r = a1
Proof
rw[] >> metis_tac[is_refl_equiv_to_itself]
QED

Theorem compose_with_g_eq_equiv:
∀f0 f1 R A a0 a1.
         f0∶R → A ∧ f1∶R → A ∧ is_refl f0 f1 ∧
         a0∶ one → A ∧ a1∶ one → A ∧
bar f1 o
  (tp (ev A two o ⟨f0 o p1 R (exp A two),p2 R (exp A two)⟩)) o
  sg A o a0 =
bar f1 o
  (tp (ev A two o ⟨f0 o p1 R (exp A two),p2 R (exp A two)⟩)) o
  sg A o a1 ⇒
 ∃r. r∶ one → R ∧ f0 o r = a0 ∧ f1 o r = a1
Proof
rw[] >>
‘∀a'. a'∶one → A ⇒
       ((∃r. r∶one → R ∧ f0 ∘ r = a0 ∧ f1 ∘ r = a') ⇔
       ∃r. r∶one → R ∧ f0 ∘ r = a1 ∧ f1 ∘ r = a')’
 by (ho_match_mp_tac Thm6_page29_means_just_that >> rw[]) >>
    (* why metis_tac[Thm6_page29_means_just_that] does not work in this case *)
irule equiv_to_same_element >>   
metis_tac[equiv_to_same_element]
QED
    

                  
 


Theorem Thm6_page29_picture:
∀f0 f1 a0 a1 R A.
 f0∶ R → A ∧ f1∶ R → A ∧ is_symm f0 f1 ∧ is_trans f0 f1 ∧
 a0∶ one → A ∧ a1∶ one → A ⇒
 coeqa f0 f1 ∘ a0 = coeqa f0 f1 ∘ a1 ⇒
 bar f1 o
  (tp (ev A two o ⟨f0 o p1 R (exp A two),p2 R (exp A two)⟩)) o
  sg A o a0 =
 bar f1 o
  (tp (ev A two o ⟨f0 o p1 R (exp A two),p2 R (exp A two)⟩)) o
  sg A o a1
Proof  
rw[] >>
‘(bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
          sg A) ∘ f0 =
         (bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
          sg A) ∘ f1’ by metis_tac[f0g_eq_f1g] >>
‘(bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A)∶ A → exp A two’
 by cheat >>
qabbrev_tac ‘l = (bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘ sg A)’ >>
‘(bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
        sg A) ∘ a0 =
 (bar f1 ∘ tp (ev A two ∘ ⟨f0 ∘ p1 R (exp A two),p2 R (exp A two)⟩) ∘
        sg A) ∘ a1’ suffices_by cheat >> simp[] >>
‘∃u. u∶ coeqo f0 f1 → exp A two ∧ u o coeqa f0 f1 = l’
 suffices_by
  (rw[] >>
  ‘coeqa f0 f1∶ A → coeqo f0 f1’ by metis_tac[coeqa_hom] >>
  metis_tac[compose_assoc]) >>
qexists_tac ‘coeq_induce f0 f1 l’ >> rw[] (* 2 *)
>- metis_tac[coeq_induce_hom]
>- metis_tac[coeq_fac]
QED


        

Theorem Thm6:
∀f0 f1 R A. f0∶ R → A ∧ f1∶ R → A ∧
            is_refl f0 f1 ∧ is_symm f0 f1 ∧ is_trans f0 f1 ∧
            is_mono ⟨f0, f1⟩ ⇒
            R ≅ eqo ((coeqa f0 f1) o p1 A A)
                    ((coeqa f0 f1) o p2 A A)
Proof
rw[] >> irule Thm6_first_sentence >> rw[] >>
irule equiv_to_same_element >> rw[] >> qexists_tac ‘A’ >>
simp[] >> 
ho_match_mp_tac Thm6_page29_means_just_that >> rw[] >>
irule Thm6_page29_picture >> rw[]
QED                    

val _ = export_theory();
