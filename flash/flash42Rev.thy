theory flash42Rev imports flashPub
begin
section{*Main defintions*}
lemma NI_FAckVsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_FAck ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvVsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Inv  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvAck_1VsInv42:  
    (*newRule2VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv3 \<le> N" and  a6:"iInv1~=iInv2  " and  a7:"iInv1~=iInv3  " and  a8:"iInv2~=iInv3  " and  a9:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_InvAck_1  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>iRule2=iInv3)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>iRule2=iInv3)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv3\<and>iRule2=iInv1)   \<or>(iRule1=iInv3\<and>iRule2=iInv2)   \<or>(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_InvAck_1_HomeVsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_InvAck_1_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvAck_2VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_InvAck_2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_GetXVsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_GetX_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv3) )  ( Const UNI_PutX ))  )    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_Nak1VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_GetX_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_Nak2VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_GetX_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_Nak3VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_GetX_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX1VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX2VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX3VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX3 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX4VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX4 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX5VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX5 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX6VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX6 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX7VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX7 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX8VsInv42:  
    (*newRule2VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv3 \<le> N" and  a6:"iInv1~=iInv2  " and  a7:"iInv1~=iInv3  " and  a8:"iInv2~=iInv3  " and  a9:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX8 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>iRule2=iInv3)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>iRule2=iInv3)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv3\<and>iRule2=iInv1)   \<or>(iRule1=iInv3\<and>iRule2=iInv2)   \<or>(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv1)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv2)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX8_homeVsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX8_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX9VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX9 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX10VsInv42:  
    (*newRule2VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv3 \<le> N" and  a6:"iInv1~=iInv2  " and  a7:"iInv1~=iInv3  " and  a8:"iInv2~=iInv3  " and  a9:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX10 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>iRule2=iInv3)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>iRule2=iInv3)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv3\<and>iRule2=iInv1)   \<or>(iRule1=iInv3\<and>iRule2=iInv2)   \<or>(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv1)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv2)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX10_homeVsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX10_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX11VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_GetX_PutX11 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_GetVsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_Get_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Nak1VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Nak2VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_Get_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Nak3VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_Get_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Put1VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_Get_Put1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Put2VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_Get_Put2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Put3VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_Get_Put3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_PutVsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_PutXAcksDoneVsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Local_PutXAcksDone ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_NakVsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Nak  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Nak_ClearVsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Nak_Clear ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Nak_HomeVsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Nak_Home ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_GetX_NakVsInv42:  
    (*newRule2VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv3 \<le> N" and  a6:"iInv1~=iInv2  " and  a7:"iInv1~=iInv3  " and  a8:"iInv2~=iInv3  " and  a9:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Remote_GetX_Nak  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>iRule2=iInv3)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>iRule2=iInv3)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv3\<and>iRule2=iInv1)   \<or>(iRule1=iInv3\<and>iRule2=iInv2)   \<or>(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
 
lemma NI_Remote_GetX_Nak_HomeVsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Remote_GetX_Nak_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
 
 
     

lemma lemmaOnPtrAtGetX[intro]:
  assumes  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 
    and a5:"formEval ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX )) s" and
    a6:"formEval   ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2)) s " and
    a7:"\<forall>f. f \<in> (invariants   N) \<longrightarrow> formEval f s "
 shows  "formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2) )  s"
 proof(rule ccontr)
  assume b0:"\<not>formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2) )  s"
  have b1:"formEval (inv2 iInv1 iInv2) s"
    apply(cut_tac a7)
    
    apply(drule_tac x="inv2  iInv1 iInv2" in spec)
    apply(cut_tac a7 a2 a3 a4,simp)
    done
 with b0 a5 a6 show False
  by auto
qed  



lemma lemmaOnPtrAtGet[intro]:
  assumes  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 
    and a5:"formEval ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get )) s" and
    a6:"formEval   ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2)) s " and
    a7:"\<forall>f. f \<in> (invariants   N) \<longrightarrow> formEval f s "
 shows  "formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2) )  s"
 proof(rule ccontr)
  assume b0:"\<not>formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2) )  s"
  have b1:"formEval (inv3 iInv1 iInv2) s"
    apply(cut_tac a7)
    
    apply(drule_tac x="inv3  iInv1 iInv2" in spec)
    apply(cut_tac a7 a2 a3 a4,simp)
    done
 with b0 a5 a6 show False
  by auto
qed  

lemma lemmaOnPtr1[intro]:
  assumes  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 
    and a5:"formEval ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get )) s" and
    a6:"formEval   ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2)) s " and
    a7:"\<forall>f. f \<in> (invariants   N) \<longrightarrow> formEval f s " and
    b2:"iInv1' \<le> N" and  b3:"iInv2' \<le> N" and  b4:"iInv1'~=iInv2'  " 
    and b5:"formEval ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1') )  ( Const UNI_Get )) s" and
    b6:"formEval   ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1') )   (Const iInv2')) s " and
    b7:"iInv2\<noteq>iInv2'"
 shows False
 proof -
  have c1:"formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2) )  s"
    by(metis a2 a3 a4 a5 a6 a7 lemmaOnPtrAtGet)
  have c2:"formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2') )  s"
    by(metis b2 b3 b4 b5 b6 a7 lemmaOnPtrAtGet)
 with c1 b7  show False
  by auto
qed  


lemma lemmaOnPtr2[intro]:
  assumes  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 
    and a5:"formEval ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX )) s" and
    a6:"formEval   ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2)) s " and
    a7:"\<forall>f. f \<in> (invariants   N) \<longrightarrow> formEval f s " and
    b2:"iInv1' \<le> N" and  b3:"iInv2' \<le> N" and  b4:"iInv1'~=iInv2'  " 
    and b5:"formEval ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1') )  ( Const UNI_GetX )) s" and
    b6:"formEval   ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1') )   (Const iInv2')) s " and
    b7:"iInv2\<noteq>iInv2'"
 shows False
 proof -
  have c1:"formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2) )  s"
    by(metis a2 a3 a4 a5 a6 a7 lemmaOnPtrAtGetX)
  have c2:"formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2') )  s"
    by(metis b2 b3 b4 b5 b6 a7 lemmaOnPtrAtGetX)
 with c1 b7  show False
  by auto
qed 


lemma lemmaOnPtr3[intro]:
  assumes  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 
    and a5:"formEval ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get )) s" and
    a6:"formEval   ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2)) s " and
    a7:"\<forall>f. f \<in> (invariants   N) \<longrightarrow> formEval f s " and
    b2:"iInv1' \<le> N" and  b3:"iInv2' \<le> N" and  b4:"iInv1'~=iInv2'  " 
    and b5:"formEval ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1') )  ( Const UNI_GetX )) s" and
    b6:"formEval   ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1') )   (Const iInv2')) s " and
    b7:"iInv2\<noteq>iInv2'"
 shows False
 proof -
  have c1:"formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2) )  s"
    by(metis a2 a3 a4 a5 a6 a7 lemmaOnPtrAtGet)
  have c2:"formEval ( eqn ( IVar ( Global ''Dir_HeadPtr'') )   (Const iInv2') )  s"
    by(metis b2 b3 b4 b5 b6 a7 lemmaOnPtrAtGetX)
 with c1 b7  show False
  by auto
qed      

  lemma NI_Remote_GetX_PutXVsInv42Aux:  
    (*newRule2VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv3 \<le> N" and  a6:"iInv1~=iInv2  " and  a7:"iInv1~=iInv3  " and  a8:"iInv2~=iInv3  " and  a9:"iRule1~=iRule2  " 

  shows  "invHoldForRule'' s (inv42  iInv1  iInv2  iInv3 ) (NI_Remote_GetX_PutX  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>iRule2=iInv3)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>iRule2=iInv3)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv3\<and>iRule2=iInv1)   \<or>(iRule1=iInv3\<and>iRule2=iInv2)   \<or>(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv1)"

      have "invHoldForRule3' s (inv42  iInv1  iInv2  iInv3 ) (NI_Remote_GetX_PutX  iRule1  iRule2 ) (invariants   N)"            
     

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''CacheState'' iInv1) )  ( Const CACHE_E ))  ) ) " in exI,auto)
 
        
        done
      then  have "?P3 s" by (rule weak3)
       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv2)"

                  
      have "invHoldForRule3' s (inv42  iInv1  iInv2  iInv3 ) (NI_Remote_GetX_PutX  iRule1  iRule2 ) (invariants   N)"      

         
        apply(   cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv3) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  )    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv3) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

        then  have "?P3 s" by (rule weak3)
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

       have "?P3 s"           
       proof( unfold invHoldForRule3''_def,simp only:Let_def,( rule impI)+,                   rule ccontr)
                    assume c1:"\<forall>f'. f' \<in> invariants N \<longrightarrow> formEval f' s" and c2:"formEval (pre (NI_Remote_GetX_PutX iRule1 iRule2)) s "
                    and c3:"\<not> formEval (substFormByStatement (inv42 iInv1 iInv2 iInv3) (act (NI_Remote_GetX_PutX iRule1 iRule2))) s"
                   have d1:" formEval (eqn (IVar (Para ''UniMsg_Cmd'' iInv1)) (Const UNI_GetX)) s" by(cut_tac a5 a6 a7 a8 b1 c2 c3, auto)
                   have d2:"formEval (eqn (IVar (Para ''UniMsg_Cmd'' iRule1)) (Const UNI_GetX)) s" by(cut_tac b1 c2 c3, auto)
                   have d3:"formEval (eqn (IVar (Para ''UniMsg_proc'' iInv1)) (Const iInv2)) s"  by(cut_tac b1 c2 c3, auto)
                   have d4:"formEval (eqn (IVar (Para ''UniMsg_proc'' iRule1)) (Const iRule2)) s"  by(cut_tac b1 c2 c3, auto)
                    show False thm lemmaOnPtr2
                    apply(cut_tac a1 a2 a3 a4 a5 a6 b1 c1 c2 c3 d1 d2 d3 d4,blast )
                    done
                   qed

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     
  

 qed
 
  lemma NI_Remote_GetX_PutXVsInv42:  
    (*newRule2VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv3 \<le> N" and  a6:"iInv1~=iInv2  " and  a7:"iInv1~=iInv3  " and  a8:"iInv2~=iInv3  " and  a9:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Remote_GetX_PutX  iRule1  iRule2 ) (invariants   N)"
by (metis NI_Remote_GetX_PutXVsInv42Aux a2 a3 a4 a5 a6 a7 a8 a9 local.a1 strengthEn) 
  
lemma NI_Remote_GetX_PutX_HomeVsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Remote_GetX_PutX_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_Get_Nak1VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Remote_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_Get_Nak2VsInv42:  
    (*newRule2VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv3 \<le> N" and  a6:"iInv1~=iInv2  " and  a7:"iInv1~=iInv3  " and  a8:"iInv2~=iInv3  " and  a9:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Remote_Get_Nak2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>iRule2=iInv3)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>iRule2=iInv3)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv3\<and>iRule2=iInv1)   \<or>(iRule1=iInv3\<and>iRule2=iInv2)   \<or>(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_Get_Put1VsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Remote_Get_Put1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_Get_Put2VsInv42:  
    (*newRule2VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv3 \<le> N" and  a6:"iInv1~=iInv2  " and  a7:"iInv1~=iInv3  " and  a8:"iInv2~=iInv3  " and  a9:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Remote_Get_Put2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>iRule2=iInv3)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>iRule2=iInv3)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1=iInv3\<and>iRule2=iInv1)   \<or>(iRule1=iInv3\<and>iRule2=iInv2)   \<or>(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))   \<or>(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv3)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 \<and>iRule2~=iInv3 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 )"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  a8  a9  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_PutVsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Remote_Put  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_PutXVsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_ReplaceVsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ReplaceHomeVsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_ReplaceHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ReplaceHomeShrVldVsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_ReplaceHomeShrVld ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ReplaceShrVldVsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_ReplaceShrVld  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ShWbVsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_ShWb N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_WbVsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (NI_Wb ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_GetX1VsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (PI_Local_GetX_GetX1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_GetX2VsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (PI_Local_GetX_GetX2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_PutX1VsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (PI_Local_GetX_PutX1 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_PutX2VsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (PI_Local_GetX_PutX2 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_PutX3VsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (PI_Local_GetX_PutX3 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_PutX4VsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (PI_Local_GetX_PutX4 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_Get_GetVsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (PI_Local_Get_Get ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_Get_PutVsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (PI_Local_Get_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_PutXVsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (PI_Local_PutX ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_ReplaceVsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (PI_Local_Replace ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Remote_GetVsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (PI_Remote_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma PI_Remote_GetXVsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (PI_Remote_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>(iRule1=iInv3)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  a7  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv3)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 \<and>iRule1~=iInv3 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  a7  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma PI_Remote_PutXVsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (PI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Remote_ReplaceVsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (PI_Remote_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma StoreVsInv42:  
    (*Rule1VsPInv3*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv3 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iInv1~=iInv3  " and  a7:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (Store  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma StoreHomeVsInv42:  
    (*Rule0VsPInv3*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv3 \<le> N" and  a4:"iInv1~=iInv2  " and  a5:"iInv1~=iInv3  " and  a6:"iInv2~=iInv3  " 

  shows  "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) (StoreHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     
     by (cut_tac a1 a2 a3 a4 a5, auto  ) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  end
