from typing import Match, Tuple
import re
import glob
import difflib


def remove_residue(conjunct: str):
    conj_new = re.sub(r'\\<and>$', r'', conjunct)
    conj_new = re.sub(r'\\<and> \\<comment>\\<open>.*\\<close>', '', conj_new)
    conj_new = re.sub(r'\\<and> $', r'', conj_new)
    #print(conj_new)
    return conj_new


def get_conjuncts():
    coh_pattern: re.Pattern = re.compile(r'SWMR_state_machine T = \(((?:[^\"]|\s)*)\)')
    with open("Common/CoherenceProperties.thy", 'r') as coh_file:
        coh_prop: str = coh_file.read()

    coh_prop = re.sub(re.escape('C_msg_P_oppo ISD (nextHTDDataPending) (\<lambda> T i. \<not> CSTATE Modified T i) T'), f'C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T', coh_prop)
    #coh_prop = re.sub(re.escape('\<lambda> T i'), f'\<lambda>T i', coh_prop)
    coh_prop = re.sub(re.escape('(nextHTDDataPending)'), 'nextHTDDataPending', coh_prop)
    coh_tuple: list[str] = coh_pattern.findall(coh_prop)
    conj_pattern = re.compile(r'(.*)(?:\\<and>|\s+)\s')
    conjuncts: list[str] = conj_pattern.findall(coh_tuple[0])
    conjuncts = list(map(remove_residue, conjuncts))
    #for conj in conjuncts:
        #print(conj)
    return conjuncts

def transform_isabelle_file(input_filename: str) -> str:
    match: Match = re.match(r"(Fix)(\w+)\.thy", input_filename)
    if not match:
        raise ValueError("Filename does not match the expected pattern in label40.py.")
   
    prefix1,  name = match.groups()
    output_filename: str = f"Fix{name}.thy"
    
    with open(input_filename, 'r') as file:
        content: str = file.read()

    theory_new_name = f"Fix{name}"
    content = re.sub(r'(theory\s+)\w+', r'\1 ' + theory_new_name, content)

    facts_pattern: re.Pattern = re.compile(r'have.*(i(\d{1,4})): "(.*?)".*by.*insert.*')
    facts_to_transform = facts_pattern.findall(content)
    
    
    counter = int(facts_to_transform[-1][1])
    print(facts_to_transform[-1])
    print("counter", counter)
    
    new_facts_list: list[str] = []
    all_conjs = get_conjuncts()
    all_conjs_indexed = zip(range(len(all_conjs) - 50, len(all_conjs) + 1), all_conjs[len(all_conjs) - 50:])
    print(all_conjs[-1])
    for conjuncts in all_conjs_indexed:
        (i, conjunct) = conjuncts
        if(i == 45 or i == 46):
            continue
        if re.compile(r'.*C_msg_state RdOwn IMAD.*').findall(conjunct) != []:
            continue
        if re.compile(r'.*length \(reqs1 T\).*1.*length \(reqs2 T\).*1').findall(conjunct) != []:
            continue
        if re.compile(r'.*length \(snps2 T\).*1.*length \(snps1 T\).*1').findall(conjunct) != []:
            continue
        #print(i, "#"*100)
        conjr = re.compile(r'(have|and).*(i\d{1,4}).*' + re.escape(conjunct))
        fact = conjr.findall(content)
        if(fact == []):
            #if((conjunct.strip())[0] == '('):
                #conjr = re.compile(r'(have|and).*(i\d{1,4}).*\(' + re.escape((conjunct.strip())) + '\)')
            #else: 
            conjr = re.compile(r'(have|and).*(i\d{1,4}).*' + re.escape(conjunct.strip()))
            conjr2 = re.compile(r'(have|and).*(i\d{1,4}).*' + re.escape(conjunct.strip()[1:-1]))
            conjr3 = re.compile(r'(have|and).*(i\d{1,4}).*' + f'(' + re.escape(conjunct.strip()) + f')')
            fact = conjr.findall(content)
            if fact == []:
                fact = conjr2.findall(content)
                if fact == []:
                    fact = conjr3.findall(content)
                    if(fact == []):
                        counter += 1
                        new_facts_list.append(f'have i{counter}: "' + conjunct + '" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)')

                    #else: 
                        #print("fact" + fact[0][1] + f"found for conjunct {i}")
                #else:
                    #print("fact" + fact[0][1] + f"found for conjunct {i}")
            #else:
                #print("fact" + fact[0][1] + f"found for conjunct {i}")
        #else:
            #print("fact" + fact[0][1] + f"found for conjunct {i}")

    #for fact in facts_to_transform:
    #    fact_id: str = fact[1]  # Extract the ID without the 'i'


    #    #fact_content: str = replace_T_preserving_whitespace(fact[3])
    #    #fact_r = re.compile(r'show.*(r\d{1,4})b?:.*' + re.escape(fact_content))
    #    
    #    subgoal = fact_r.findall(content)
    #    if(subgoal == []):
    #        fact_r = re.compile(r'show.*(r\d{1,4})b?:.*' + re.escape(fact_content.strip()))
    #        subgoal = fact_r.findall(content)
    #    if(subgoal == []):
    #        new_goal: str = f"  show r{fact_id}b: \"{fact_content}\"\nsledgehammer sorry"
    #        new_facts_list.append(new_goal)
    #        print(fact_id + 'b', "added")
    #content = re.sub(r'.*have.*i162.*".*".*\n', '', content)
    #content = re.sub(r'.*have.*i163.*".*".*\n', '', content)
    #content = re.sub(r'.*(have|and).*i\d{2}:.*C_msg_state RdOwn IMAD T.*\n', '', content)
    #content = re.sub(r'.*have i\d{3}:.*reqs1 T \\<noteq> \[\] \\<longrightarrow> snpresps1 T = \[\].*\n', '', content)
    #content = re.sub(r'.*have i\d{3}:.*reqs2 T \\<noteq> \[\] \\<longrightarrow> snpresps2 T = \[\].*\n', '', content)
    #content = re.sub(r'.*have i\d{3}:.*snpresps1 T \\<noteq> \[\] \\<longrightarrow> htddatas1 T = \[\].*\n', '', content)
    #content = re.sub(r'.*have i\d{3}:.*snpresps2 T \\<noteq> \[\] \\<longrightarrow> htddatas2 T = \[\].*\n', '', content)
    #content = re.sub(r'.*have i.*C_msg_state RdOwn IMAD.*\n', '', content)
    #content = re.sub(r'.*show r\d{2,3}.*C_msg_state RdOwn IMAD.*\n', '', content)
    #content = re.sub(r'.*show r\d{2}.*C_msg_P_oppo IIA \(nextGOPendingIs GO_WritePull\) \(\\<lambda>T i. \\<not> nextSnoopPending T i\).*\n(.*\n){1,4}.*by.*\n', '', content)
    #content = re.sub(r'.*show r\d{2}.*C_msg_P_oppo IIA \(nextGOPendingIs GO_WritePull\) \(\\<lambda>T i. \\<not> nextSnoopPending T i\).*\n(.*\n){1,4}.*by.*\n', '', content)
    #content = re.sub(r'show r1\d{2}.*snpresps.*\n.*htddatas.*\n(.*\n){1,3}.*by.*\n', '', content)
    #content = re.sub(r'.*have.*i.*length \(reqs1 T\).*1.*length \(reqs2 T\).*1.*by.*insert assms.*\n', '', content)
    #content = re.sub(r'.*have.*i\d{3}.*CSTATE IMAD T.*nextHTDDataPending T.*HSTATE ModifiedM T(\s|\))*".*by.*insert assms.*\n', '', content)
    #content = re.sub(r'.*have.*i\d{3}.*CSTATE IIA T.*HSTATE ModifiedM T.*CSTATE Modified T.*CSTATE MIA T \d(\s|\))*".*by.*insert assms.*\n', '', content)
    #content = re.sub(r'.*have.*i151.*CSTATE Invalid T 0.*CSTATE ISDI T 0.*HSTATE ModifiedM T.*CSTATE Modified T 1.*CSTATE MIA T 1.*".*by.*insert.*assms.*\n', '', content)
    #content = re.sub(r'.*have.*i152.*CSTATE Invalid T 1.*CSTATE ISDI T 1.*HSTATE ModifiedM T.*CSTATE Modified T 0.*CSTATE MIA T 0.*".*by.*insert.*assms.*\n', '', content)
    #content = re.sub(r'.*have.*i10[2-3].*HSTATE ModifiedM T.*nextReqIsRdOwn T \d.*CSTATE Modified T \d.*CSTATE MIA T \d.*CSTATE IMAD T \d.*CSTATE SMAD T \d.*CSTATE IMA T \d.*CSTATE SMA T \d.*CSTATE IMD T \d.*CSTATE SMD T \d.*\n', '', content)
    #content = re.sub(r'have i41\d: "\(\(CSTATE Invalid T \d .*CSTATE ISDI T \d\) .* HSTATE ModifiedM T .*CSTATE Modified T \d .* CSTATE MIA T \d .* CSTATE IMAD T \d .* nextHTDDataPending T \d .* nextGOPending T \d .* CSTATE IMA T \d .* nextGOPending T \d .* CSTATE IMD T \d .* nextHTDDataPending T \d\) ".*\n', '', content) 
    #content = re.sub(r'have i411: "\(HSTATE MD T .* nextDTHDataFrom 0 T .*CSTATE IMAD T 1 .* nextHTDDataPending T 1 .* CSTATE IMD T 1\).* by \(insert assms, unfold SWMR_state_machine_def, elim conjE, assumption\)', '', content)
    #content = re.sub(r'have i412: "\(HSTATE MD T .* nextDTHDataFrom 1 T .*CSTATE IMAD T 0 .* nextHTDDataPending T 0 .* CSTATE IMD T 0\).* by \(insert assms, unfold SWMR_state_machine_def, elim conjE, assumption\)', '', content)
    #content = re.sub(r'show r102: "\(HSTATE ModifiedM \(.*\)  .* nextReqIs RdOwn \(.*\) 0 .*\(CSTATE Modified \(.*\) 1 .* CSTATE MIA \(.*\) 1 .* CSTATE IMAD \(.*\) 1 .* CSTATE SMAD \(.*\) 1 .* CSTATE IMA \(.*\) 1 .* CSTATE SMA \(.*\) 1 .* CSTATE IMD \(.*\) 1 .* CSTATE SMD \(.*\) 1\)\) ".*\n(\s)*.*by.*\n(\s)*', '', content)
    #content = re.sub(r'show r103: "\(HSTATE ModifiedM \(.*\)  .* nextReqIs RdOwn \(.*\) 1 .*\(CSTATE Modified \(.*\) 0 .* CSTATE MIA \(.*\) 0 .* CSTATE IMAD \(.*\) 0 .* CSTATE SMAD \(.*\) 0 .* CSTATE IMA \(.*\) 0 .* CSTATE SMA \(.*\) 0 .* CSTATE IMD \(.*\) 0 .* CSTATE SMD \(.*\) 0\)\) ".*\n(\s)*.*by.*\n(\s)*', '', content)
    #content = re.sub(r'show r151: "\(\(CSTATE Invalid \(.*\) 0 .* CSTATE ISDI \(.*\) 0\) .* HSTATE ModifiedM \(.*\) .*CSTATE Modified \(.*\) 1 .* CSTATE MIA \(.*\) 1\) ".*\n(\s)*.*by.*\n(\s)*', '', content)
    #content = re.sub(r'show r152: "\(\(CSTATE Invalid \(.*\) 1 .* CSTATE ISDI \(.*\) 1\) .* HSTATE ModifiedM \(.*\) .*CSTATE Modified \(.*\) 0 .* CSTATE MIA \(.*\) 0\) ".*\n(\s)*.*by.*\n(\s)*', '', content)
    #content = re.sub(r'show r155: "\(CSTATE IMAD \(.*\) 0 .* nextHTDDataPending \(.*\) 0 .*\<not> HSTATE ModifiedM \(.*\)\) ".*\n(\s)*.*by.*\n(\s)*', '', content)
    #content = re.sub(r'show r156b: "\(CSTATE IMAD \(.*\) 1 .* nextHTDDataPending \(.*\) 1 .*\<not> HSTATE ModifiedM \(.*\) \) ".*\n(\s)*.*by.*\n(\s)*', '', content)
    #content = re.sub(r'show r174: "\(CSTATE IIA \(.*\) 0 .* HSTATE ModifiedM \(.*\) .*CSTATE Modified \(.*\) 1 .* CSTATE MIA \(.*\) 1\) ".*\n(\s)*.*by.*\n(\s)*', '', content)
    #content = re.sub(r'show r175: "\(CSTATE IIA \(.*\) 1 .* HSTATE ModifiedM \(.*\) .*CSTATE Modified \(.*\) 0 .* CSTATE MIA \(.*\) 0\) ".*\n(\s)*.*by.*\n(\s)*', '', content)
    #content = re.sub(r'show r415b: "\(\(CSTATE Invalid \(.*\) 0 .* CSTATE ISDI \(.*\) 0\) .* HSTATE ModifiedM \(.*\) .*CSTATE Modified \(.*\) 1 .* CSTATE MIA \(.*\) 1 .* CSTATE IMAD \(.*\) 1 .* nextHTDDataPending \(.*\) 1 .* nextGOPending \(.*\) 1 .* CSTATE IMA \(.*\) 1 .* nextGOPending \(.*\) 1 .* CSTATE IMD \(.*\) 1 .* nextHTDDataPending \(.*\) 1\) ".*\n(\s)*.*by.*\n(\s)*', '', content)
    #content = re.sub(r'show r416b: "\(\(CSTATE Invalid \(.*\) 1 .* CSTATE ISDI \(.*\) 1\) .* HSTATE ModifiedM \(.*\) .*CSTATE Modified \(.*\) 0 .* CSTATE MIA \(.*\) 0 .* CSTATE IMAD \(.*\) 0 .* nextHTDDataPending \(.*\) 0 .* nextGOPending \(.*\) 0 .* CSTATE IMA \(.*\) 0 .* nextGOPending \(.*\) 0 .* CSTATE IMD \(.*\) 0 .* nextHTDDataPending \(.*\) 0\) ".*\n(\s)*.*by.*\n(\s)*', '', content)
    #content = re.sub(r'show r411b: "\(HSTATE MD \(.*\) .* nextDTHDataFrom 0 \(.*\) .*CSTATE IMAD \(.*\) 1 .* nextHTDDataPending \(.*\) 1 .* CSTATE IMD \(.*\) 1\) ".*\n(\s)*.*by.*\n(\s)*', '', content)
    #content = re.sub(r'show r412b: "\(HSTATE MD \(.*\) .* nextDTHDataFrom 1 \(.*\) .*CSTATE IMAD \(.*\) 0 .* nextHTDDataPending \(.*\) 0 .* CSTATE IMD \(.*\) 0\)".*\n(\s)*.*by.*\n(\s)*', '', content)

    #content = re.sub(r'have i\d{3}: "\(CSTATE IMA T 0 .* CSTATE SMA T 0 .* \(nextHTDDataPending T 0\) .* CSTATE IMD T 0 .* CSTATE SMD T 0 .* \(\(CSTATE IMAD T 0 .* CSTATE SMAD T 0\) .* nextGOPending T 0\) .*\(\(\<not> CSTATE ISD T 1\) .* \<not> CSTATE IMD T 1 .* \<not> CSTATE SMD T 1 .* \<not>\( \(CSTATE ISAD T 1 .* CSTATE IMAD T 1 .* CSTATE SMAD T 1\) .* nextGOPending T 1\) .* \<not>CSTATE ISA T 1 .* \<not> CSTATE IMA T 1 .* \<not> CSTATE SMA T 1 .* \<not> \(  nextHTDDataPending T 1\) .*  \<not> CSTATE Shared T 1 .* \<not> CSTATE Modified T 1\)\) "   by \(insert assms, unfold SWMR_state_machine_def, elim conjE, assumption\)', '', content)
    #content = re.sub(r'have i\d{3}: "\(CSTATE IMA T 1 .* CSTATE SMA T 1 .* \(nextHTDDataPending T 1\) .* CSTATE IMD T 1 .* CSTATE SMD T 1 .* \(\(CSTATE IMAD T 1 .* CSTATE SMAD T 1\) .* nextGOPending T 1\) .*\(\(\<not> CSTATE ISD T 0\) .* \<not> CSTATE IMD T 0 .* \<not> CSTATE SMD T 0 .* \<not>\( \(CSTATE ISAD T 0 .* CSTATE IMAD T 0 .* CSTATE SMAD T 0\) .* nextGOPending T 0\) .* \<not>CSTATE ISA T 0 .* \<not> CSTATE IMA T 0 .* \<not> CSTATE SMA T 0 .* \<not> \(  nextHTDDataPending T 0\) .*  \<not> CSTATE Shared T 0 .* \<not> CSTATE Modified T 0\)\) "   by \(insert assms, unfold SWMR_state_machine_def, elim conjE, assumption\)', '', content)
    #content = re.sub(r'have i\d{3}: "\(CSTATE IMA T 0 .* CSTATE SMA T 0 .* \(nextHTDDataPending T 0\) .* CSTATE IMD T 0 .* CSTATE SMD T 0 .* \(\(CSTATE IMAD T 0 .* CSTATE SMAD T 0\) .* nextGOPending T 0\) .*dthdatas1 T = \[\] .* \(dthdatas2 T = \[\] .* HSTATE MB T\)\) "   by \(insert assms, unfold SWMR_state_machine_def, elim conjE, assumption\)', '', content)
    #content = re.sub(r'have i\d{3}: "\(CSTATE IMA T 1 .* CSTATE SMA T 1 .* \(nextHTDDataPending T 1\) .* CSTATE IMD T 1 .* CSTATE SMD T 1 .* \(\(CSTATE IMAD T 1 .* CSTATE SMAD T 1\) .* nextGOPending T 1\) .*dthdatas2 T = \[\] .* \(dthdatas1 T = \[\] .* HSTATE MB T\)\) "   by \(insert assms, unfold SWMR_state_machine_def, elim conjE, assumption\)', '', content)


    #content = re.sub(r'have i\d{3}: "\(HSTATE ModifiedM T  .* nextReqIs RdOwn T 0 .*\(CSTATE Modified T 1 .* CSTATE MIA T 1 .* CSTATE IMAD T 1 .* CSTATE SMAD T 1 .* CSTATE IMA T 1 .* CSTATE SMA T 1 .* CSTATE IMD T 1 .* CSTATE SMD T 1\)\) "   by \(insert assms, unfold SWMR_state_machine_def, elim conjE, assumption\)', '', content)
    #content = re.sub(r'have i\d{3}: "\(HSTATE ModifiedM T  .* nextReqIs RdOwn T 1 .*\(CSTATE Modified T 0 .* CSTATE MIA T 0 .* CSTATE IMAD T 0 .* CSTATE SMAD T 0 .* CSTATE IMA T 0 .* CSTATE SMA T 0 .* CSTATE IMD T 0 .* CSTATE SMD T 0\)\) "   by \(insert assms, unfold SWMR_state_machine_def, elim conjE, assumption\)', '', content)




    #content = re.sub(r'have i\d{3}: "\(HSTATE MD T .* nextDTHDataFrom 0 T .*CSTATE IMAD T 1 .* nextHTDDataPending T 1 .* CSTATE IMD T 1\) " by \(insert assms, unfold SWMR_state_machine_def, elim conjE, assumption\)', '', content)
    #content = re.sub(r'have i\d{3}: "\(HSTATE MD T .* nextDTHDataFrom 1 T .*CSTATE IMAD T 0 .* nextHTDDataPending T 0 .* CSTATE IMD T 0\)" by \(insert assms, unfold SWMR_state_machine_def, elim conjE, assumption\)', '', content)
    #
    #content = re.sub(r'show r\d{3}: "\(CSTATE ISAD .* 1 .*snpresps2 .* = \[\]\) "\s+.*by.*\n', '', content)
    #
    #
    #content = re.sub(r'show r\d{3}: "\(CSTATE ISAD .* 0 .*snpresps1 .* = \[\]\) "\s+.*by.*\n', '', content)
    #
    #
    #content = re.sub(r'show r\d{3}: "\(CSTATE IMAD .* 0 .* nextHTDDataPending .* 0 .*\<not> HSTATE ModifiedM .*\) "\s+.*by.*\n', '', content)
    #
    #
    #content = re.sub(r'show r\d{3}: "\(CSTATE IMAD .* 1 .* nextHTDDataPending .* 1 .*\<not> HSTATE ModifiedM .* \) "\s+.*by.*\n', '', content)

    #content = re.sub(r'show r\d{3}: "\(HSTATE ModifiedM .* .* CSTATE IIA .* 0 .*dthdatas1 .* = \[\] .* dthdatas2 .* = \[\]\) "\s+.*by.*\n', '', content)
    #content = re.sub(r'show r\d{3}: "\(HSTATE ModifiedM .* .* CSTATE IIA .* 1 .*dthdatas1 .* = \[\] .* dthdatas2 .* = \[\]\) "\s+.*by.*\n', '', content)
    #
    #content = re.sub(r'have i\d{3}: "\(\(CSTATE ISAD T 0 .* nextGOPending T 0\) .* CSTATE ISA T 0 .* \( nextHTDDataPending T 0\) .* CSTATE Shared T 0 .*\<not> CSTATE Modified T 1 .* dthdatas1 T = \[\] .* \(dthdatas2 T = \[\] .* HSTATE SB T\)\) "   by \(insert assms, unfold SWMR_state_machine_def, elim conjE, assumption\).*\n', '', content)
    #content = re.sub(r'have i\d{3}: "\(\(CSTATE ISAD T 1 .* nextGOPending T 1\) .* CSTATE ISA T 1 .* \( nextHTDDataPending T 1\) .* CSTATE Shared T 1 .*\<not> CSTATE Modified T 0 .* dthdatas2 T = \[\] .* \(dthdatas1 T = \[\] .* HSTATE SB T\)\) "   by \(insert assms, unfold SWMR_state_machine_def, elim conjE, assumption\).*\n', '', content)
    #
    #content = re.sub(r'show r\d{3}: "\(\(CSTATE ISAD .* 0 .* nextGOPending .* 0\) .* CSTATE ISA .* 0 .* \( nextHTDDataPending .* 0\) .* CSTATE Shared .* 0 .*\<not> CSTATE Modified .* 1 .* dthdatas1 .* = \[\] .* \(dthdatas2 .* = \[\] .* HSTATE SB .*\)\) ".*\n', '', content)
    #content = re.sub(r'have aux\d{3}: " dthdatas2 T = \[\]".*\n', '', content)
    #
    #
    #content = re.sub(r'show r\d{3}: "\(\(CSTATE ISAD .* 1 .* nextGOPending .* 1\) .* CSTATE ISA .* 1 .* \( nextHTDDataPending .* 1\) .* CSTATE Shared .* 1 .*\<not> CSTATE Modified .* 0 .* dthdatas2 .* = \[\] .* \(dthdatas1 .* = \[\] .* HSTATE SB .*\)\) ".*\n', '', content)

    #content = re.sub(r'.*have.*True.*by.*\n', '', content)
    #content = re.sub(r'.*and.*True".*\n', '', content)
    #content = re.sub(r'.*show.*True.*\n\s+.*by.*\n', '', content)
    #content = re.sub(r'have i\d{3}: "\(length \(snps2 T\) .* 1   .* length \(snps1 T\) .* 1\) " by \(insert assms, unfold SWMR_state_machine_def, elim conjE, assumption\).*\n', '', content)
    #content = re.sub(r'.*have i12[2-3]:.*\n', '', content)
    




    new_goals: str = '\n' + "\n".join(new_facts_list)
    #big_lemma_pattern = re.compile(r'(lemma .*coherent_aux_simpler.*\n(.*\n)*.*show r\d{3}:.*\n(.*\n){1,3})(\s)+qed')
    big_lemma_header_pattern = re.compile(r'(.*\n)*:?((.*\n).*by \(insert assms, unfold SWMR_state_machine_def, elim conjE, assumption\))')
    big_lemma = big_lemma_header_pattern.search(content)
    new_goals = new_goals 
    transformed_content: str = content[:big_lemma.end(2)] + new_goals + content[big_lemma.end(2):] #+ content[lemma_match.start(1):lemma_match.start(3)] + new_goals + "\n" + content[lemma_match.start(3):]
    print(content[big_lemma.end(2) - 100:big_lemma.end(2)])
    print(new_goals)
    #transformed_content = re.sub(r'have i\d{3}: "\(length \(snps2 T\) .* 1   .* length \(snps1 T\) .* 1\) " by \(insert assms, unfold SWMR_state_machine_def, elim conjE, assumption\).*\n', '', transformed_content)




    
    with open(output_filename, 'w') as file:
        file.write(transformed_content)
    
    return output_filename

if __name__ == "__main__":
    
    #files = glob.glob("FixSharedRdOwn.thy")
    files = (glob.glob("Fix*.thy")) + (glob.glob("patch*.thy"))#+ ["lemmaHeaders.thy"] # - set(glob.glob("Fix*Backup.thy")) - set(glob.glob("Fix*AlmostDone.thy")))
    for file_path in files:
        print("doing", file_path)
        input_filename: str = file_path #sys.argv[1]
        if(input_filename == "M3_SimpleHostMDDirtyEvict.thy"):
            print("No trans needed for MDDE")
            continue;
        try:
            output_filename: str = transform_isabelle_file(input_filename)
            print(f"Transformation complete. {output_filename}")
        except ValueError as e:
            print(f"Error: {e}")

