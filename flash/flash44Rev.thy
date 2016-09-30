theory flash44Rev imports flashPub
begin
section{*Main defintions*}
lemma NI_FAckVsInv44:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_FAck ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvVsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Inv  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1  a2  a3  a4 , auto)
 lemma NI_InvAck_1VsInv44:  
    (*Rule2VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_InvAck_1  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3 a4 a5 a6,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvAck_1_HomeVsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_InvAck_1_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1  a2  a3  a4 , auto)
 lemma NI_InvAck_2VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_InvAck_2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1  a2  a3  a4 , auto)
 lemma NI_Local_GetX_GetXVsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_GetX_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Get ))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_Nak1VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_GetX_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_Nak2VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_GetX_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_Nak3VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_GetX_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX1VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_GetX_PutX1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX2VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_GetX_PutX2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX3VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_GetX_PutX3 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX4VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_GetX_PutX4 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX5VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_GetX_PutX5 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX6VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_GetX_PutX6 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX7VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_GetX_PutX7 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX8VsInv44:  
    (*Rule2VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_GetX_PutX8 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX8_homeVsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_GetX_PutX8_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX9VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_GetX_PutX9 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX10VsInv44:  
    (*Rule2VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_GetX_PutX10 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX10_homeVsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_GetX_PutX10_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX11VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_GetX_PutX11 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_GetVsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_Get_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_Get ))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Nak1VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Nak2VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_Get_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Nak3VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_Get_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Put1VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_Get_Put1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Put2VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_Get_Put2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Put3VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_Get_Put3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_PutVsInv44:  
  (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
  fix s 
 
  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Local_PutXAcksDoneVsInv44:  
  (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Local_PutXAcksDone ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
  fix s 
 
  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_NakVsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Nak  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Nak_ClearVsInv44:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Nak_Clear ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Nak_HomeVsInv44:  
  (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Nak_Home ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
  fix s 
 
  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Remote_GetX_NakVsInv44:  
    (*Rule2VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Remote_GetX_Nak  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_GetX_Nak_HomeVsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Remote_GetX_Nak_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_GetX_PutXVsInv44:  
    (*Rule2VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Remote_GetX_PutX  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_GetX_PutX_HomeVsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Remote_GetX_PutX_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_Get_Nak1VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Remote_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_Get_Nak2VsInv44:  
    (*Rule2VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Remote_Get_Nak2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_Get_Put1VsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Remote_Get_Put1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_Get_Put2VsInv44:  
    (*Rule2VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iInv2 \<le> N" and  a5:"iInv1~=iInv2  " and  a6:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Remote_Get_Put2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1\<and>iRule2=iInv2)   \<or>(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>(iRule1=iInv2\<and>iRule2=iInv1)   \<or>(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  a5  a6  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>iRule2=iInv2)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>iRule2=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 )\<and>(iRule2~=iInv1 \<and>iRule2~=iInv2 ))"

                  have "?P1 s \<or> ?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  a5  a6  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_PutVsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Remote_Put  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_PutXVsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_ReplaceVsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1  a2  a3  a4 , auto)
 lemma NI_ReplaceHomeVsInv44:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_ReplaceHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ReplaceHomeShrVldVsInv44:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_ReplaceHomeShrVld ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ReplaceShrVldVsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_ReplaceShrVld  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1  a2  a3  a4 , auto)
 lemma NI_ShWbVsInv44:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_ShWb N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_WbVsInv44:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (NI_Wb ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_GetX1VsInv44:  
  (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (PI_Local_GetX_GetX1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
  fix s 
 
  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_GetX_GetX2VsInv44:  
  (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (PI_Local_GetX_GetX2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
  fix s 
 
  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_GetX_PutX1VsInv44:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (PI_Local_GetX_PutX1 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_PutX2VsInv44:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (PI_Local_GetX_PutX2 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_PutX3VsInv44:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (PI_Local_GetX_PutX3 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_GetX_PutX4VsInv44:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (PI_Local_GetX_PutX4 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_Get_GetVsInv44:  
  (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (PI_Local_Get_Get ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -
  fix s 
 
  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Global ''Dir_Pending'') )  ( Const false ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iInv1) )   (Const iInv2))  ) ) " in exI,auto)
 
        
        done

       
       then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

        by blast

  


 qed
lemma PI_Local_Get_PutVsInv44:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (PI_Local_Get_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_PutXVsInv44:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (PI_Local_PutX ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Local_ReplaceVsInv44:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (PI_Local_Replace ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Remote_GetVsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (PI_Remote_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma PI_Remote_GetXVsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (PI_Remote_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>(iRule1=iInv2)   \<or>((iRule1~=iInv1 \<and>iRule1~=iInv2 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"(iRule1=iInv2)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 \<and>iRule1~=iInv2 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma PI_Remote_PutXVsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (PI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1  a2  a3  a4 , auto)
 lemma PI_Remote_ReplaceVsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (PI_Remote_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1  a2  a3  a4 , auto)
 lemma StoreVsInv44:  
    (*Rule1VsPInv2*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" and  a3:"iInv2 \<le> N" and  a4:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (Store  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1  a2  a3  a4 , auto)
 lemma StoreHomeVsInv44:  
    (*Rule0VsPInv2*)
  assumes   a1:"iInv1 \<le> N" and  a2:"iInv2 \<le> N" and  a3:"iInv1~=iInv2  " 

  shows  "invHoldForRule' s (inv44  iInv1  iInv2 ) (StoreHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3, auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  end
