%%%%%%%%%% Rule Based Expert System Shell %%%%%%%%%%
%%%
%%% This is the expert system with the example from the textbook:
%%%
%%% Artificial Intelligence: 
%%% Structures and strategies for complex problem solving
%%%
%%% by George F. Luger and William A. Stubblefield
%%% 
%%% These programs are copyrighted by Benjamin//Cummings Publishers.
%%%
%%% Modified by Shaun-inn Wu
%%%
%%% These program are offered for educational purposes only.
%%%
%%% Disclaimer: These programs are provided with no warranty whatsoever as to
%%% their correctness, reliability, or any other property.  We have written 
%%% them for specific educational purposes, and have made no effort
%%% to produce commercial quality computer programs.  Please do not expect 
%%% more of them then we have intended.
%%%
%%% This code has been tested with SWI-Prolog (Multi-threaded, Version 7.6.4)
%%% and appears to function as intended.


% solve(Goal): solve(fix_car(Advice)) for the car problem.
% Top level call.  Initializes working memory; attempts to solve Goal
% with certainty factor; prints results; asks user if they would like a
% trace.

solve(Goal) :- 
    init, print_help,
    solve(Goal,C,[],1),
    nl,write('Solved '),write(Goal),
    write(' With Certainty = '),write(C),nl,nl,
    ask_for_trace(Goal).

% init
% purges all facts from working memory.

init :- retractm(fact(X)), retractm(untrue(X)).

% solve(Goal,CF,Rulestack,Cutoff_context)
% Attempts to solve Goal by backwards chaining on rules;  CF is
% certainty factor of final conclusion; Rulestack is stack of
% rules, used in why queries, Cutoff_context is either 1 or -1
% depending on whether goal is to be proved true or false
% (e.g. not Goal requires Goal be false in oreder to succeed).

solve(true,100,Rules,_).

solve(A,100,Rules,_) :- 
    fact(A).

solve(A,-100,Rules,_) :-
    untrue(A).

solve(not(A),C,Rules,T) :- 
    T2 is -1 * T,
    solve(A,C1,Rules,T2),
    C is -1 * C1.

solve((A,B),C,Rules,T) :- 
    solve(A,C1,Rules,T), 
    above_threshold(C1,T),
    solve(B,C2,Rules,T),
    above_threshold(C2,T),
    minimum(C1,C2,C).

solve(A,C,Rules,T) :- 
    rule((A :- B),C1), 
    solve(B,C2,[rule(A,B,C1)|Rules],T),
    C is (C1 * C2) / 100,
    above_threshold(C,T).

solve(A,C,Rules,T) :- 
    rule((A), C),
    above_threshold(C,T).

solve(A,C,Rules,T) :- 
    askable(A), 
    not(known(A)), 
    ask(A,Answer),
    respond(Answer,A,C,Rules).

% respond( Answer, Query, CF, Rule_stack).
% respond will process Answer (yes, no, how, why, help).
% asserting to working memory (yes or no)
% displaying current rule from rulestack (why)
% showing proof trace of a goal (how(Goal)
% displaying help (help).
% Invalid responses are detected and the query is repeated.

respond(Bad_answer,A,C,Rules) :- 
    not(member(Bad_answer,[help, yes,no,why,how(_)])),
    write('answer must be either help, (y)es, (n)o, (h)ow(X), (w)hy'),nl,nl,
    ask(A,Answer),
    respond(Answer,A,C,Rules).

respond(yes,A,100,_) :- 
    assert(fact(A)).

respond(no,A,-100,_) :- 
    assert(untrue(A)).

respond(why,A,C,[Rule|Rules]) :- 
    display_rule(Rule),
    ask(A,Answer),
    respond(Answer,A,C,Rules).

respond(why,A,C,[]) :-
    write('Back to goal, no more explanation  possible'),nl,nl,
    ask(A,Answer),
    respond(Answer,A,C,[]).

respond(how(Goal),A,C,Rules) :- 
    respond_how(Goal),
    ask(A,Answer),
    respond(Answer,A,C,Rules).

respond(help,A,C,Rules) :- 
    print_help,
    ask(A,Answer),
    respond(Answer,A,C,Rules).

% ask(Query, Answer)
% Writes Query and reads the Answer.  Abbreviations (y, n, h, w) are
% trnslated to appropriate command be filter_abbreviations

ask(Query,Answer) :- 
    display_query(Query),
    read(A),
    filter_abbreviations(A,Answer),!.

% filter_abbreviations( Answer, Command)
% filter_abbreviations will expand Answer into Command.  If
% Answer is not a known abbreviation, then Command = Answer.

filter_abbreviations(y,yes).
filter_abbreviations(n,no).
filter_abbreviations(w,why).
filter_abbreviations(h,help).
filter_abbreviations(h(X),how(X)).
filter_abbreviations(X,X).

% known(Goal)
% Succeeds if Goal is known to be either true or untrue.

known(Goal) :- fact(Goal).
known(Goal) :- untrue(Goal).

% ask_for_trace(Goal).
% Invoked at the end of a consultation, ask_for_trace asks the user if
% they would like a trace of the reasoning to a goal.

ask_for_trace(Goal) :-
    write('Trace of reasoning to goal ? '),
    read(Answer),nl,
    show_trace(Answer,Goal),!.

% show_trace(Answer,Goal)
% If Answer is ``yes'' or ``y,'' show trace will display  a trace
% of Goal, as in a ``how'' query.  Otherwise, it succeeds, doing nothing.

show_trace(yes,Goal) :- respond_how(Goal).

show_trace(y,Goal) :- respond_how(Goal).

show_trace(_,_).

% print_help
% Prints a help screen.

print_help :- 
    write('Exshell allows the following responses to queries:'),nl,nl,
    write('   yes - query is known to be true.'),nl,
    write('   no - query is false.'),nl,
    write('   why - displays rule currently under consideration.'),nl,
    write('   how(X) - if X has been inferred, displays trace of reasoning.'),nl,
    write('   help - prints this message.'),nl,
    write('   Your response may be abbreviated to the first letter and must end with a period (.).'),nl.

% display_query(Goal)
% Shows Goal to user in the form of a query.

display_query(Goal) :-
    write(Goal),
    write('? ').

% display_rule(rule(Head, Premise, CF))
% prints rule in IF...THEN form.

display_rule(rule(Head,Premise,CF)) :-
    write('IF       '),
    write_conjunction(Premise),
    write('THEN     '),
    write(Head),nl,
    write('CF   '),write(CF),
    nl,nl.

% write_conjunction(A)
% write_conjunction will print the components of a rule premise.  If any
% are known to be true, they are so marked.

write_conjunction((A,B)) :-
    write(A), flag_if_known(A),!, nl,
    write('     AND '),
    write_conjunction(B).

write_conjunction(A) :- write(A),flag_if_known(A),!, nl.

% flag_if_known(Goal).
% Called by write_conjunction, if Goal follows from current state
% of working memory, prints an indication, with CF.

flag_if_known(Goal) :- 
    build_proof(Goal,C,_,1), 
    write('     ***Known, Certainty = '),write(C).

flag_if_known(A). 

% Predicates concerned with how queries.

% respond_how(Goal).
% calls build_proof to determine if goal follows from current state of working
% memory.  If it does, prints a trace of reasoning, if not, so indicates.

respond_how(Goal) :- 
    build_proof(Goal,C,Proof,1),
    interpret(Proof),nl,!.

respond_how(Goal) :- 
    build_proof(Goal,C,Proof,-1),
    interpret(Proof),nl,!.

respond_how(Goal) :- 
    write('Goal does not follow at this stage of consultation.'),nl.

% build_proof(Goal, CF, Proof, Cutoff_context).
% Attempts to prove Goal, placing a trace of the proof in Proof.
% Functins the same as solve, except it does not ask for unknown information.
% Thus, it only proves goals that follow from the rule base and the current 
% contents of working memory.

build_proof(true,100,(true,100),_).

build_proof(Goal, 100, (Goal :- given,100),_) :- fact(Goal).

build_proof(Goal, -100, (Goal :- given,-100),_) :- untrue(Goal).

build_proof(not(Goal), C, (not(Proof),C),T) :- 
    T2 is -1 * T,
    build_proof(Goal,C1,Proof,T2),
    C is -1 * C1.

build_proof((A,B),C,(ProofA, ProofB),T) :-
    build_proof(A,C1,ProofA,T),
    above_threshold(C1,T),
    build_proof(B,C2,ProofB,T),
    above_threshold(C2,T),
    minimum(C1,C2,C).

build_proof(A, C, (A :- Proof,C),T) :-
    rule((A :- B),C1), 
    build_proof(B, C2, Proof,T),
    C is (C1 * C2) / 100,
    above_threshold(C,T).

build_proof(A, C, (A :- true,C),T) :-
    rule((A),C),
    above_threshold(C,T).

% interpret(Proof).
% Interprets a Proof as constructed by build_proof,
% printing a trace for the user.

interpret((Proof1,Proof2)) :-
    interpret(Proof1),interpret(Proof2).

interpret((Goal :- given,C)):-
    write(Goal),
    write(' was given. CF = '), write(C),nl,nl.

interpret((not(Proof), C)) :-
    extract_body(Proof,Goal),
    write('not '),
    write(Goal),
    write(' CF = '), write(C),nl,nl,
    interpret(Proof).

interpret((Goal :- true,C)) :-
    write(Goal),
        write(' is a fact, CF = '),write(C),nl.

interpret(Proof) :-
    is_rule(Proof,Head,Body,Proof1,C),
    nl,write(Head),write(' CF = '),
    write(C), nl,write('was proved using the rule'),nl,nl,
    rule((Head :- Body),CF),
    display_rule(rule(Head, Body,CF)), nl,
    interpret(Proof1).

% isrule(Proof,Goal,Body,Proof,CF)
% If Proof is of the form Goal :- Proof, extracts
% rule Body from Proof.

is_rule((Goal :- Proof,C),Goal, Body, Proof,C) :-
    not(member(Proof, [true,given])),
    extract_body(Proof,Body).

% extract_body(Proof).
% extracts the body of the top level rule from Proof.

extract_body((not(Proof), C), (not(Body))) :-
    extract_body(Proof,Body).

extract_body((Proof1,Proof2),(Body1,Body2)) :-
    !,extract_body(Proof1,Body1),
    extract_body(Proof2,Body2).

extract_body((Goal :- Proof,C),Goal).
    
% Utility Predicates.

retractm(X) :- retract(X), fail.
retractm(X) :- retract((X:-Y)), fail.
retractm(X).

member(X,[X|_]).
member(X,[_|T]) :- member(X,T).

minimum(X,Y,X) :- X =< Y.
minimum(X,Y,Y) :- Y < X.

above_threshold(X,1) :- X >= 20.
above_threshold(X,-1) :- X =< -20.



%%%
%%% Knowledge base for cardiovascular diseases.
%%%

rule((cardioDisease(Advice):-
		disease(Y), cure(Y,Advice)),100).


rule((disease(arrythmia1):-
issues(heart_arrythmic), lightheadedness, racing_heartbeat),80). 

rule((disease(arrythmia2):-
issues(heart_arrythmic), lightheadedness, not(racing_heartbeat), slow_heartbeat),75).

rule((disease(atherosclerosis1):-
issues(narrowing_of_arteries), loss_of_vision, trouble_speaking),85).

rule((disease(atherosclerosis2):-
issues(narrowing_of_arteries), loss_of_vision, not(trouble_speaking)),75).

rule((disease(coronary_artery_disease1):-
issues(heart_attack),  palpitation, lightheadedness, feeling_of_indigestion),80).

rule((disease(coronary_artery_disease2):-
issues(heart_attack), not(palpitation), lightheadedness, feeling_of_indigestion),75).

rule((disease(coronary_artery_disease3):-
issues(heart_attack), not(palpitation), not(lightheadedness), feeling_of_indigestion),65).

rule((disease(cardiomyopathy1):-
issues(heart_muscle_disease), chest_pain, fatigue, shortness_of_breath, abdominal_bloating), 85).

rule((disease(cardiomyopathy2):-
issues(heart_muscle_disease), chest_pain, shortness_of_breath, not(fatigue), not(abdominal_bloating)), 60).

rule((disease(heart_valve_disease1):-
issues(heartvalve_problem), rapid_weight_gain, abdominal_swelling, palpitation),80).

rule((disease(heart_valve_disease2):-
issues(heartvalve_problem), rapid_weight_gain, abdominal_swelling, not(palpitation)),70).

rule((disease(heart_valve_disease3):-
issues(heartvalve_problem), rapid_weight_gain, not(abdominal_swelling) , not(palpitation)),60).

rule((disease(rheumatic_heart_disease1):-
issues(heartvalve_problem), fever, skin_rashes, joint_pain),90).

rule((disease(rheumatic_heart_disease2):-
issues(heartvalve_problem), fever, skin_rashes, not(joint_pain)),80).


%%% Inference rules

rule((issues(heart_arrythmic):-
chest_pain, shortness_of_breath, palpitation, fainting), 85).

rule((issues(narrowing_of_arteries):-
chest_pain, shortness_of_breath, not(palpitation), numbness_in_arms_legs),75).

rule((issues(heart_attack):-
chest_pain, shortness_of_breath, nausea, upperbody_pain),90).

rule((issues(heart_muscle_disease):-
not(nausea), swelling_in_legs_or_ankles, racing_heartbeat, fainting),85).

rule((issues(heartvalve_problem):-
chest_pain, swelling_in_legs_or_ankles, not(racing_heartbeat), shortness_of_breath, fatigue),75).







rule(cure(arrythmia1, 'Person is suffering from Arrhythmia. \n Precheckup done at casualty department \n Flow of treatment : \n Following tests are recommended by Casualty medical officer to confirm its presence : \n\n 1. ECG test: It records electrical activity of your heart. ECG measures the timing and duration of each electrical phase in your heartbeat. \n\n2. Holter monitor : It is portable ECG gadget which can be worn for a day or longer to monitor movement of your heart while you go about your daily activities. \n\n3. Event monitor : It checks heart rhythm of your heart, tells you whether your heart rhythm is functioning properly or not. \n\n4. Echocardiogram :- This uses ultrasound wave to reveal picture of your heart. Result of this test determine whether all things in your heart properly functioning or not. \n\n5. Implantable loop recorder : It records your hearts electrical activity continuously. \n\n6. Head-up tilt table test: In this test, as you lie flat on a table, your heart rate and blood pressure are tracked. The table is then rotated so that you can stand up at it. Your doctor will monitor how the heart and the nervous system that regulates it respond to the angle shift. '),100).

rule(cure(arrythmia2, 'Person is suffering from Arrhythmia. \n Precheckup done at casualty department \n Flow of treatment : \n Following tests are recommended by Casualty medical officer to confirm its presence : \n\n 1. ECG test: It records electrical activity of your heart. ECG measures the timing and duration of each electrical phase in your heartbeat. \n\n2. Holter monitor : It is portable ECG gadget which can be worn for a day or longer to monitor movement of your heart while you go about your daily activities. \n\n3. Event monitor : It checks heart rhythm of your heart, tells you whether your heart rhythm is functioning properly or not. \n\n4. Echocardiogram :- This uses ultrasound wave to reveal picture of your heart. Result of this test determine whether all things in your heart properly functioning or not. \n\n5. Implantable loop recorder : It records your hearts electrical activity continuously. \n\n6. Head-up tilt table test: In this test, as you lie flat on a table, your heart rate and blood pressure are tracked. The table is then rotated so that you can stand up at it. Your doctor will monitor how the heart and the nervous system that regulates it respond to the angle shift. '),100).

rule(cure(atherosclerosis1,'Person is suffering from Atherosclerosis. \n Precheckup done at casualty department \n Flow of treatment : \n Following tests are recommended by Casualty medical officer to confirm its presence : \n\n 1. Blood test : To check your blood sugar and cholesterol levels. High levels of blood sugar and cholesterol raise your risk of atherosclerosis. \n\n 2. Stress test : It monitors heart rate & blood-pressure during exercise. \n\n 3.EKG test: Monitors electrical signals in patients heart to look for areas which have reduced flow of blood. \n\n 4. Cardiac angiogram : Patient need to do this test as this test is crucial and shows if patients arteries are narrowed or not. During this test, a thin catheter tube is inserted into patients heart and blood vessels, dye flows through catheter. As dye fills arteries, artery becomes visible on x ray & it reveal areas of arteries blockage. \n\n 5. CT scan : To find out narrowed arteries. \n\n 6. Ankle Brachial Index (ABI test) : In this test, doctor compares blood flow in patient legs with blood flow in arms. This test tells whether you have atherosclerosis in artery of your legs or feet. \n\n 7. Doppler ultrasound test : It uses soundwaves to create picture of artery which shows if there is blockage in artery.'),100).

rule(cure(atherosclerosis2,'Person is suffering from Atherosclerosis. \n Precheckup done at casualty department \n Flow of treatment : \n Following tests are recommended by Casualty medical officer to confirm its presence : \n\n 1. Blood test : To check your blood sugar and cholesterol levels. High levels of blood sugar and cholesterol raise your risk of atherosclerosis. \n\n 2. Stress test : It monitors heart rate & blood-pressure during exercise. \n\n 3.EKG test: Monitors electrical signals in patients heart to look for areas which have reduced flow of blood. \n\n 4. Cardiac angiogram : Patient need to do this test as this test is crucial and shows if patients arteries are narrowed or not. During this test, a thin catheter tube is inserted into patients heart and blood vessels, dye flows through catheter. As dye fills arteries, artery becomes visible on x ray & it reveal areas of arteries blockage. \n\n 5. CT scan : To find out narrowed arteries. \n\n 6. Ankle Brachial Index (ABI test) : In this test, doctor compares blood flow in patient legs with blood flow in arms. This test tells whether you have atherosclerosis in artery of your legs or feet. \n\n 7. Doppler ultrasound test : It uses soundwaves to create picture of artery which shows if there is blockage in artery.'),100).

rule(cure(coronary_artery_disease1, 'Person is suffering from Coronary Artery Disease. \n Precheckup done at casualty department \n Flow of treatment : \n Following tests are recommended by Casualty medical officer to confirm its presence : \n\n 1. Electrocardiogram test: It monitors electrical activity of your heart, it may help doctor to determine whether patient had heart attack previously or one that is in progress. \n\n 2. Echocardiogram :- This uses ultrasound wave to reveal picture of heart of the patient. Result of this test determine whether all things in your heart properly functioning or not. \n\n 3. Heart CT scan : It helps doctor to check for deposit of calcium in your artery. \n\n 4. Exercise stress test:  It monitors heart rate & blood-pressure during exercise. \n\n 5. Cardiac catherization : In this test, a thin catheter tube is inserted in your  coronary artery in your legs or arm upto your heart, X-rays used to guide right position to the catheter. In some cases, dye is inserted through catheter into your artery to find out the blockages in the arteries.'),100).
rule(cure(coronary_artery_disease2, 'Person is suffering from Coronary Artery Disease. \n Precheckup done at casualty department \n Flow of treatment : \n Following tests are recommended by Casualty medical officer to confirm its presence : \n\n 1. Electrocardiogram test: It monitors electrical activity of your heart, it may help doctor to determine whether patient had heart attack previously or one that is in progress. \n\n 2. Echocardiogram :- This uses ultrasound wave to reveal picture of heart of the patient. Result of this test determine whether all things in your heart properly functioning or not. \n\n 3. Heart CT scan : It helps doctor to check for deposit of calcium in your artery. \n\n 4. Exercise stress test: It monitors heart rate & blood-pressure during exercise.  \n\n 5. Cardiac catherization : In this test, a thin catheter tube is inserted in your  coronary artery in your legs or arm upto your heart, X-rays used to guide right position to the catheter. In some cases, dye is inserted through catheter into your artery to find out the blockages in the arteries.'),100).
rule(cure(coronary_artery_disease3, 'Person is suffering from Coronary Artery Disease. \n Precheckup done at casualty department \n Flow of treatment : \n Following tests are recommended by Casualty medical officer to confirm its presence : \n\n 1. Electrocardiogram test: It monitors electrical activity of your heart, it may help doctor to determine whether patient had heart attack previously or one that is in progress. \n\n 2. Echocardiogram :- This uses ultrasound wave to reveal picture of heart of the patient. Result of this test determine whether all things in your heart properly functioning or not. \n\n 3. Heart CT scan : It helps doctor to check for deposit of calcium in your artery. \n\n 4. Exercise stress test: It monitors heart rate & blood-pressure during exercise.  \n\n 5. Cardiac catherization : In this test, a thin catheter tube is inserted in your  coronary artery in your legs or arm upto your heart, X-rays used to guide right position to the catheter. In some cases, dye is inserted through catheter into your artery to find out the blockages in the arteries.'),100).

rule(cure(cardiomyopathy1, 'Person is suffering from Cardiomyopathy. \n Precheckup done at casualty department \n Flow of treatment : \n Following tests are recommended by Casualty medical officer to confirm its presence :  \n\n1. Chest x-ray : To check for enlargement of the heart or fluid on the lungs. \n\n 2. CT scan: In this test, X-ray tube insode machine rotate around the body of patient & collect heart & chest images to assess size of heart & function.  \n\n 3. MRI scan : This test use radiowaves & magnetic field to create the heart images. \n\n 4. Blood test : To check your kidney, thyroid and liver function and to measure your iron levels. \n\n 5. Genetic testing or screening: Genetic testing, also known as DNA testing, is used to identify changes in DNA sequence or chromosome structure. It can be used to reveal cardiomyopathy. '),100).
rule(cure(cardiomyopathy2, 'Person is suffering from Cardiomyopathy. \n Precheckup done at casualty department \n Flow of treatment : \n Following tests are recommended by Casualty medical officer to confirm its presence : \n\n1. Chest x-ray : To check for enlargement of the heart or fluid on the lungs. \n\n 2. CT scan: In this test, X-ray tube insode machine rotate around the body of patient & collect heart & chest images to assess size of heart & function.  \n\n 3. MRI scan : This test use radiowaves & magnetic field to create the heart images. \n\n 4. Blood test : To check your kidney, thyroid and liver function and to measure your iron levels. \n\n 5. Genetic testing or screening: Genetic testing, also known as DNA testing, is used to identify changes in DNA sequence or chromosome structure. It can be used to reveal cardiomyopathy. '),100).

rule(cure(heart_valve_disease1, 'Person is suffering from Heart Valve Disease. \n Precheckup done at casualty department \n Flow of treatment : \n Following tests are recommended by Casualty medical officer to confirm its presence : \n\n 1. Doppler ultrasound test : This test detects changes in flow of blood across heart valves & pressure within the heart chambers. \n\n 2. ECG test  : This test shows the electrical activity of your heart & check for abnormal heart rhythm. \n\n 3. Cardiac Magnetic Resonance Imaging scanning test : The picture of the hearts valves and chambers is created using a large magnet and radio waves. It can produce moving images of the heart while it is pumping and detect abnormal blood flow.  \n\n 4. Transesophageal echocardiography : During this test, soundwave transducer is placed on end of special tube and passed into mouth & down the food pipe. This lets doctor get a close look at heart chambers, valves & back of heart. \n\n 5. Myocardial strain imaging:  This test check for changes in function of your heart. \n\n 6. 3D echo : This echo test display the parts of the heart in 3D so the doctor can more completely measure the size & check function of valves of heart.'),100).

rule(cure(heart_valve_disease2, 'Person is suffering from Heart Valve Disease. \n Precheckup done at casualty department \n Flow of treatment : \n Following tests are recommended by Casualty medical officer to confirm its presence : \n\n 1. Doppler ultrasound test : This test detects changes in flow of blood across heart valves & pressure within the heart chambers. \n\n 2. ECG test  : This test shows the electrical activity of your heart & check for abnormal heart rhythm. \n\n 3. Cardiac Magnetic Resonance Imaging scanning test : The picture of the hearts valves and chambers is created using a large magnet and radio waves. It can produce moving images of the heart while it is pumping and detect abnormal blood flow.  \n\n 4. Transesophageal echocardiography : During this test, soundwave transducer is placed on end of special tube and passed into mouth & down the food pipe. This lets doctor get a close look at heart chambers, valves & back of heart. \n\n 5. Myocardial strain imaging:  This test check for changes in function of your heart. \n\n 6. 3D echo : This echo test display the parts of the heart in 3D so the doctor can more completely measure the size & check function of valves of heart.'),100).

rule(cure(heart_valve_disease3, 'Person is suffering from Heart Valve Disease. \n Precheckup done at casualty department \n Flow of treatment : \n Following tests are recommended by Casualty medical officer to confirm its presence : \n\n 1. Doppler ultrasound test : This test detects changes in flow of blood across heart valves & pressure within the heart chambers. \n\n 2. ECG test  : This test shows the electrical activity of your heart & check for abnormal heart rhythm. \n\n 3. Cardiac Magnetic Resonance Imaging scanning test : The picture of the hearts valves and chambers is created using a large magnet and radio waves. It can produce moving images of the heart while it is pumping and detect abnormal blood flow.  \n\n 4. Transesophageal echocardiography : During this test, soundwave transducer is placed on end of special tube and passed into mouth & down the food pipe. This lets doctor get a close look at heart chambers, valves & back of heart. \n\n 5. Myocardial strain imaging:  This test check for changes in function of your heart. \n\n 6. 3D echo : This echo test display the parts of the heart in 3D so the doctor can more completely measure the size & check function of valves of heart.'),100).

rule(cure(rheumatic_heart_disease1, 'Person is suffering from Rheumatic Heart Disease. \n Precheckup done at casualty department \n Flow of treatment : \n Following tests are recommended by Casualty medical officer to confirm its presence : \n\n1. Chest x-ray : To check for enlargement of the heart or fluid on the lungs. \n\n2. Electrocardiogram (ECG) : To check if the chambers of the heart have enlarged \n\n3. Echocardiogram : To check the heart valves for any damage or infection and assessing if there is heart failure. This is the most useful test for finding out if RHD is present. '),100).
rule(cure(rheumatic_heart_disease2, 'Person is suffering from Rheumatic Heart Disease. \n Precheckup done at casualty department \n Flow of treatment : \n Following tests are recommended by Casualty medical officer to confirm its presence : \n\n1. Chest x-ray : To check for enlargement of the heart or fluid on the lungs. \n\n2. Electrocardiogram (ECG) : To check if the chambers of the heart have enlarged \n\n3. Echocardiogram : To check the heart valves for any damage or infection and assessing if there is heart failure. This is the most useful test for finding out if RHD is present. '),100).


askable(feeling_of_indigestion).
askable(slow_heartbeat).
askable(abdominal_swelling).
askable(loss_of_vision).
askable(chest_pain).
askable(shortness_of_breath).
askable(lightheadedness).
askable(fatigue).
askable(nausea).
askable(palpitation).
askable(fainting).
askable(abdominal_bloating).
askable(racing_heartbeat).
askable(swelling_in_legs_or_ankles).
askable(rapid_weight_gain).
askable(fever).
askable(numbness_in_arms_legs).
askable(joint_pain).
askable(upperbody_pain).
askable(trouble_speaking).
askable(skin_rashes).