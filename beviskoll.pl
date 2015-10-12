% Lab 1 in Logic in Computer Science course
% Authors:
%           Lucas Ljungberg <lucaslj@kth.se>
%           Anton Ronsjö    <ronsjo@kth.se>
%


verify(InputFileName) :-
    see(InputFileName), read(Prems), read(Goal), read(Proof),
    seen,
    valid_proof(Prems, Goal, Proof).

valid_proof(Prems, Goal, Proof) :-
    check_goal(Goal, Proof)
    .

%% iterate() :-
    

%% Checks if the last line of proof matches with goal 
check_goal(Goal, Proof) :-
    last(Proof, ProofLine),         %% Gets the last line of proof.
    nth0(1, ProofLine, GoalMatch),  %% Extracts the middle part of the line.
    Goal = GoalMatch.               %% Checks if Goal matches the last line of proof.