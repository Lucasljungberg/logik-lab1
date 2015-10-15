% Lab 1 in Logic in Computer Science course
% Authors:
%           Lucas Ljungberg <lucaslj@kth.se>
%           Anton Ronsjö    <ronsjo@kth.se>
%

%% Startpoint of the program.
verify(InputFileName) :-
    see(InputFileName), read(Prems), read(Goal), read(Proof),
    seen,
    valid_goal(Goal, Proof),
    valid_proof(Prems, Proof).

valid_goal(Goal, Proof) :-
    get_last(Proof, MatchedGoal),
    writeln(MatchedGoal),
    Goal = MatchedGoal, !.

get_last([H, []], H).
get_last([_, T], H) :- get_last(T, H).

valid_proof(Prems, Proof).
