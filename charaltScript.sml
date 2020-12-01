open HolKernel Parse boolLib bossLib;

val _ = new_theory "charalt";

Theorem is_pb_thm:
∀X Y Z P p q f g. f∶ X → Z ∧ g∶ Y→ Z ⇒ 
  (is_pb P p q f g <=> p∶ P → X ∧ q∶ P → Y /\
                      f o p = g o q ∧
                      (∀A u v. u∶ A → X ∧ v∶ A → Y ∧ f o u = g o v ⇒
                      ∃!a. a∶ A → P ∧ p o a = u ∧ q o a = v))
Proof
rw[is_pb_def,hom_def]
QED          


Theorem pb_exists':
∀f g. cod f = cod g ⇒
       ∃P p q. p∶ P → dom f ∧ q∶ P → dom g ∧ f o p = g o q ∧
            (∀A u v. u∶ A → dom f ∧ v∶ A → dom g ∧ f o u = g o v ⇒
             ∃!a. a∶ A → P ∧ p o a = u ∧ q o a = v)
Proof
rw[] >>
qabbrev_tac ‘X = dom f’ >> qabbrev_tac ‘Z = cod f’ >>
qabbrev_tac ‘Y = dom g’ >>
‘g∶ Y → Z’ by (simp[Abbr‘Y’,Abbr‘Z’] >> metis_tac[hom_def]) >>
‘f∶ X → Z’ by (simp[Abbr‘X’,Abbr‘Z’] >> metis_tac[hom_def]) >>
drule pb_exists >> rw[]
QED

Theorem pb_exists_thm = SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] pb_exists'        


val pb_def = new_specification ("pb_def",["pbo","pb1","pb2"],pb_exists_thm)

Theorem pb_thm:
∀X Y Z f g.
 f∶ X → Z ∧ g∶ Y → Z ⇒
 pb1 f g∶ pbo f g → X ∧ pb2 f g∶ pbo f g → Y ∧
 f o pb1 f g = g o pb2 f g ∧
 (∀A u v. u∶ A → X ∧ v∶ A → Y ∧ f o u = g o v ⇒
          ∃!a. a∶ A → pbo f g ∧ pb1 f g o a = u ∧ pb2 f g o a = v)    
Proof
strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
strip_tac >>
‘cod f = cod g’ by metis_tac[hom_def] >>
drule pb_def >> simp[hom_def] >> rw[] (* 3 *)
>>metis_tac[hom_def]
QED

Theorem is_pb_thm_one_side:
∀X Y Z P p q f g.
  is_pb P p q f g ∧ f∶X → Z ∧ g∶Y → Z ⇒
   p∶P → X ∧ q∶P → Y ∧ f ∘ p = g ∘ q ∧
   ∀A u v.
     u∶A → X ∧ v∶A → Y ∧ f ∘ u = g ∘ v ⇒
     ∃!a. a∶A → P ∧ p ∘ a = u ∧ q ∘ a = v   
Proof
strip_tac >> strip_tac >> strip_tac >>
strip_tac >> strip_tac >> strip_tac >>
strip_tac >> strip_tac >> strip_tac >>
‘(is_pb P p q f g ⇔
          p∶P → X ∧ q∶P → Y ∧ f ∘ p = g ∘ q ∧
          ∀A u v.
              u∶A → X ∧ v∶A → Y ∧ f ∘ u = g ∘ v ⇒
              ∃!a. a∶A → P ∧ p ∘ a = u ∧ q ∘ a = v)’
  suffices_by metis_tac[] >>
irule is_pb_thm >> metis_tac[]
QED        



Theorem pb_is_pb:
∀f g X Y Z. f∶ X → Z ∧ g∶ Y → Z ⇒
 is_pb (pbo f g) (pb1 f g) (pb2 f g) f g
Proof
simp[is_pb_def] >> strip_tac >> strip_tac >> strip_tac >>
strip_tac >> strip_tac >> strip_tac >>
‘cod f = cod g’ by metis_tac[hom_def] >>
drule pb_def >> rw[]
QED

Theorem pb_mono_mono':
∀f g X Y Z. f∶ X → Z ∧ g∶ Y → Z ∧ is_mono g ⇒
            is_mono (pb1 f g)
Proof
rw[] >>
‘is_pb (pbo f g) (pb1 f g) (pb2 f g) f g’
 by metis_tac[pb_is_pb] >>
metis_tac[pb_mono_mono]
QED

Theorem dom_one_mono:
∀f X. f∶ one → X ⇒ is_mono f
Proof
rw[] >> drule is_mono_thm >> rw[] >>
metis_tac[to1_unique]
QED

Theorem pb_fac_exists':
∀X Y Z f g.
         f∶X → Z ∧ g∶Y → Z ⇒
         ∀A u v.
             u∶A → X ∧ v∶A → Y ∧ f ∘ u = g ∘ v ⇒
             ∃a. a∶A → pbo f g ∧ pb1 f g ∘ a = u ∧ pb2 f g ∘ a = v
Proof
rw[] >>
‘pb1 f g∶pbo f g → X ∧ pb2 f g∶pbo f g → Y ∧
         f ∘ pb1 f g = g ∘ pb2 f g ∧
         ∀A u v.
             u∶A → X ∧ v∶A → Y ∧ f ∘ u = g ∘ v ⇒
             ∃!a. a∶A → pbo f g ∧ pb1 f g ∘ a = u ∧ pb2 f g ∘ a = v’
  by (irule pb_thm >> metis_tac[]) >>
fs[EXISTS_UNIQUE_ALT] >> metis_tac[]
QED

                     
Theorem char_pb:
∀A X a. is_mono a ∧ a∶ A → X ⇒
        ∃h1 h2.
          (pb1 (char a) (i2 one one)) ∘ h1 = a ∧
          a ∘ h2 = pb1 (char a) (i2 one one) ∧
          h1∶ A → pbo (char a) (i2 one one) ∧
          h2∶ pbo (char a) (i2 one one) → A ∧
          h1 ∘ h2 = id (pbo (char a) (i2 one one)) ∧
          h2 ∘ h1 = id A
Proof
rw[] >> irule prop_2_corollary_as_subobj >>
‘i2 one one∶ one → two’ by metis_tac[i2_hom] >>
‘char a∶ X → two’ by metis_tac[char_thm] >>
‘pb1 (char a) (i2 one one)∶pbo (char a) (i2 one one) → X’
 by metis_tac[pb_thm] >>
simp[] >>
‘is_mono (pb1 (char a) (i2 one one))’
 by (irule pb_mono_mono' >>
    ‘is_mono (i2 one one)’ suffices_by metis_tac[] >>
    metis_tac[dom_one_mono]) >> simp[] >>
strip_tac (* 2 *)
>- (rw[] >>
   ‘a o x∶ one → X’ by metis_tac[compose_hom] >>
   ‘(id one)∶ one → one’ by metis_tac[id1] >>
   ‘char a o (a o x) = i2 one one o id one’
    by metis_tac[char_thm,idR] >> 
   ‘∃y. y∶ one → pbo (char a) (i2 one one) ∧
        pb1 (char a) (i2 one one) ∘ y = (a o x) ∧
        pb2 (char a) (i2 one one) ∘ y = id one’
    by (irule pb_fac_exists' >> metis_tac[]) >>
   metis_tac[])
>- (reverse (rw[]) >- metis_tac[] >>
   Q.UNDISCH_THEN
   `is_mono (pb1 (char a) (i2 one one))` (K ALL_TAC) >>
   drule char_thm >> rw[] >>
   first_x_assum drule_all >> rw[] >>
   ‘pb1 (char a) (i2 one one) ∘ y∶ one → X’
    by metis_tac[compose_hom] >>
   first_x_assum drule >> rw[] >>
   ‘char a ∘ pb1 (char a) (i2 one one) =
    i2 one one o pb2 (char a) (i2 one one)’
    by metis_tac[pb_thm] >>
   ‘char a ∘ pb1 (char a) (i2 one one) ∘ y =
    (char a ∘ pb1 (char a) (i2 one one)) ∘ y’
    by metis_tac[compose_assoc] >>
   simp[] >>
   ‘pb2 (char a) (i2 one one)∶ pbo (char a) (i2 one one) → one’
    by metis_tac[pb_thm] >>
   ‘(i2 one one ∘ pb2 (char a) (i2 one one)) ∘ y =
    i2 one one ∘ pb2 (char a) (i2 one one) ∘ y’
    by metis_tac[compose_assoc] >>
   ‘pb2 (char a) (i2 one one) ∘ y = id one’
    suffices_by metis_tac[idR] >>
   metis_tac[compose_hom,to1_unique,id1])
QED


Theorem char_square:
∀A X a. is_mono a ∧ a∶ A → X ⇒ char a ∘ a = i2 one one ∘ to1 A
Proof
rw[] >> irule fun_ext >> qexistsl_tac [‘A’,‘two’] >>
‘char a∶ X → two’ by metis_tac[char_thm] >>
‘to1 A∶ A → one’ by metis_tac[to1_hom] >>
‘i2 one one ∶ one → two’ by metis_tac[i2_hom] >>
‘char a o a∶ A → two ∧ i2 one one o to1 A∶ A → two’
 by metis_tac[compose_hom] >> simp[] >>
rw[] >>
‘char a ∘ a ∘ a' = i2 one one ∘ to1 A ∘ a'’
 suffices_by metis_tac[compose_assoc] >>
‘(to1 A) o a' = id one’ by metis_tac[to1_unique,compose_hom,id1] >>
‘char a ∘ a ∘ a' = i2 one one’ suffices_by metis_tac[idR] >>
‘a o a'∶ one → X’ by metis_tac[compose_hom] >>
metis_tac[char_thm]
QED
        

Theorem char_is_pb:
∀A X a. is_mono a ∧ a∶ A → X ⇒
        is_pb A a (to1 A) (char a) (i2 one one)
Proof
rw[] >>
‘∃h1 h2.
          (pb1 (char a) (i2 one one)) ∘ h1 = a ∧
          a ∘ h2 = pb1 (char a) (i2 one one) ∧
          h1∶ A → pbo (char a) (i2 one one) ∧
          h2∶ pbo (char a) (i2 one one) → A ∧
          h1 ∘ h2 = id (pbo (char a) (i2 one one)) ∧
          h2 ∘ h1 = id A’ by metis_tac[char_pb] >>
‘i2 one one∶ one → two’ by metis_tac[i2_hom] >> 
‘char a∶ X → two’ by metis_tac[char_thm] >>
‘is_pb (pbo (char a) (i2 one one))
       (pb1 (char a) (i2 one one)) (pb2 (char a) (i2 one one))
       (char a) (i2 one one)’ by metis_tac[pb_is_pb] >>
drule is_pb_thm >> rw[] >>
first_x_assum
(qspecl_then [‘one’,‘A’,‘a’,‘to1 A’,‘i2 one one’] assume_tac) >>
first_x_assum drule >>
‘to1 A∶A → one’ by metis_tac[to1_hom] >>
‘char a ∘ a = i2 one one ∘ to1 A’ by metis_tac[char_square] >>
rw[] >>
Q.UNDISCH_THEN
 ‘is_pb A a (to1 A) (char a) (i2 one one) ⇔
        ∀A' u v.
            u∶A' → X ∧ v∶A' → one ∧ char a ∘ u = i2 one one ∘ v ⇒
            ∃!a'. a'∶A' → A ∧ a ∘ a' = u ∧ to1 A ∘ a' = v’
(K ALL_TAC) >>
‘∃a'. a'∶A' → A ∧ a ∘ a' = u ∧ to1 A ∘ a' = v’
 suffices_by
  (rw[EXISTS_UNIQUE_THM] >> metis_tac[is_mono_thm]) >>
rename [‘v∶ Q → one’] >> drule is_pb_thm_one_side >> rw[] >>
first_x_assum drule >> rw[] >> first_x_assum drule >> rw[] >>
‘∃a'. a'∶Q → A ∧ a ∘ a' = u’
 suffices_by
  (rw[] >> qexists_tac ‘a'’ >> rw[] >>
  metis_tac[compose_hom,to1_unique]) >>
first_x_assum (qspecl_then [‘Q’,‘u’,‘v’] assume_tac) >>
first_x_assum drule_all >> rw[] >>
qpat_x_assum ‘∃!a'. _’ mp_tac >> simp[EXISTS_UNIQUE_THM] >>
strip_tac >>
Q.UNDISCH_THEN
 ‘∀a' a''.
            (a'∶Q → pbo (char a) (i2 one one) ∧
             pb1 (char a) (i2 one one) ∘ a' = u ∧
             pb2 (char a) (i2 one one) ∘ a' = v) ∧
            a''∶Q → pbo (char a) (i2 one one) ∧
            pb1 (char a) (i2 one one) ∘ a'' = u ∧
            pb2 (char a) (i2 one one) ∘ a'' = v ⇒
            a' = a''’
(K ALL_TAC) >>
qexists_tac ‘h2 o a'’ >>
‘h2 o a'∶Q → A’ by metis_tac[compose_hom] >>
simp[] >> metis_tac[compose_assoc]
QED


        
        
Theorem char_is_pb_unique:
∀A X a. is_mono a ∧ a∶ A → X ⇒
        ∀c. c∶ X → two ∧ is_pb A a (to1 A) c (i2 one one) ⇒
        c = char a
Proof
rw[] >> irule fun_ext >>
‘char a∶ X → two’ by metis_tac[char_thm] >>
qexistsl_tac [‘X’,‘two’] >> simp[] >> rw[] >>
‘c o a'∶ one → two ∧ char a o a'∶ one → two’
 by metis_tac[compose_hom] >>
irule one_to_two_eq >> rw[] >>
‘is_pb A a (to1 A) (char a) (i2 one one)’
 by metis_tac[char_is_pb] >>
drule is_pb_thm_one_side >> rw[] >>
Q.UNDISCH_THEN ‘is_pb A a (to1 A) (char a) (i2 one one)’
(K ALL_TAC) >>
drule is_pb_thm_one_side >> rw[] >>
Q.UNDISCH_THEN ‘is_pb A a (to1 A) c (i2 one one)’
(K ALL_TAC) >>
‘i2 one one ∶one → two’ by metis_tac[i2_hom] >>
first_x_assum drule >> rw[] >> first_x_assum drule >> rw[] >>
last_x_assum drule >> rw[] >> first_x_assum drule >> rw[] >>
rw[EQ_IMP_THM] (* 2 *)
>- (‘c ∘ a' = i2 one one ∘ id one’ by metis_tac[idR] >>
   last_x_assum (qspecl_then [‘one’,‘a'’,‘id one’] assume_tac) >>
   ‘∃!a''. a''∶one → A ∧ a ∘ a'' = a' ∧ to1 A ∘ a'' = id one’
    by metis_tac[id1] >>
   ‘∃a''. a''∶one → A ∧ a ∘ a'' = a' ∧ to1 A ∘ a'' = id one’
    by metis_tac[EXISTS_UNIQUE_THM] >>
   ‘char a ∘ a ∘ a'' = i2 one one’ suffices_by metis_tac[] >>
   ‘i2 one one ∘ to1 A o a'' = i2 one one’
    suffices_by metis_tac[compose_assoc] >>
   ‘to1 A o a'' = id one’ by metis_tac[compose_hom,id1,to1_unique]>>
   metis_tac[idR])
>- (‘char a ∘ a' = i2 one one ∘ id one’ by metis_tac[idR] >>
   first_x_assum (qspecl_then [‘one’,‘a'’,‘id one’] assume_tac) >>
    ‘∃!a''. a''∶one → A ∧ a ∘ a'' = a' ∧ to1 A ∘ a'' = id one’
    by metis_tac[id1] >>
   ‘∃a''. a''∶one → A ∧ a ∘ a'' = a' ∧ to1 A ∘ a'' = id one’
    by metis_tac[EXISTS_UNIQUE_THM] >>
   ‘c ∘ a ∘ a'' = i2 one one’ suffices_by metis_tac[] >>
   ‘i2 one one ∘ to1 A o a'' = i2 one one’
    suffices_by metis_tac[compose_assoc] >>
   ‘to1 A o a'' = id one’ by metis_tac[compose_hom,id1,to1_unique]>>
   metis_tac[idR])
QED   

Theorem iso_subobj_same_char:
∀A B X a b h1 h2.
  is_mono a ∧ is_mono b ∧ a∶ A → X ∧ b∶ B → X ∧
  h1∶ A → B /\ h2∶ B → A /\ h1 o h2 = id B /\ h2 o h1 = id A /\
  b o h1 = a /\ a o h2 = b ==>
  char a = char b
Proof
rw[] >>
irule char_is_pb_unique >> simp[] >>
qabbrev_tac ‘b = a o h2’ >>
qexistsl_tac [‘B’,‘X’] >>
‘char a ∶X → two’ by metis_tac[char_thm] >> rw[] >>
drule is_pb_thm >> rw[] >>
first_x_assum
 (qspecl_then [‘one’,‘B’,‘b’,‘(to1 B)’,‘i2 one one’] assume_tac) >>
‘i2 one one∶ one → two’ by metis_tac[i2_hom] >>
first_x_assum drule >> simp[] >>
‘to1 B∶B → one’ by metis_tac[to1_hom] >>
‘char (b ∘ h1) ∘ b = i2 one one ∘ to1 B’
 by
  (‘char (b ∘ h1) ∘ b o id B = i2 one one ∘ to1 B’
   suffices_by metis_tac[idR] >>
  ‘char (b ∘ h1) ∘ b o h1 o h2 = i2 one one ∘ to1 B’
   suffices_by metis_tac[] >>
  ‘(char (b ∘ h1) ∘ b ∘ h1) ∘ h2 = i2 one one ∘ to1 B’
   suffices_by metis_tac[compose_assoc_4_3_left] >>
  ‘char (b ∘ h1) ∘ b ∘ h1 = i2 one one o to1 A’
   by metis_tac[char_square] >>
  simp[] >>
  ‘to1 A ∘ h2 = to1 B’
   suffices_by metis_tac[to1_hom,compose_assoc] >>
  metis_tac[to1_hom,compose_hom,to1_unique]) >>
simp[] >> rw[] >>
rename [‘v∶ Q → one’] >>
‘∃a. a∶Q → B ∧ b ∘ a = u ∧ to1 B ∘ a = v’ suffices_by
 (rw[EXISTS_UNIQUE_THM] >> metis_tac[is_mono_thm]) >>
‘∃a. a∶Q → B ∧ b ∘ a = u’ suffices_by
 (rw[] >> qexists_tac ‘a’ >> metis_tac[compose_hom,to1_unique]) >>
‘is_pb A (b ∘ h1) (to1 A) (char (b ∘ h1)) (i2 one one)’
 by metis_tac[char_is_pb] >>
drule is_pb_thm_one_side >> rw[] >>
first_x_assum drule >> rw[] >> first_x_assum drule >> rw[] >>
first_x_assum (qspecl_then [‘Q’,‘u’,‘v’] assume_tac) >>
‘∃!a. a∶Q → A ∧ (b ∘ h1) ∘ a = u ∧ to1 A ∘ a = v’
 by metis_tac[] >>
‘∃a. a∶Q → A ∧ (b ∘ h1) ∘ a = u ∧ to1 A ∘ a = v’
 by metis_tac[EXISTS_UNIQUE_THM] >>
‘h1 o a∶Q → B’ by metis_tac[compose_hom] >>
qexists_tac ‘h1 o a’ >> rw[] >> metis_tac[compose_assoc]
QED

        



val _ = export_theory();

