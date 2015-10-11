% Lab 1 in Logic in Computer Science course
% Authors:
%           Lucas Ljungberg <lucaslj@kth.se>
%           Anton Ronsjö    <ronsjo@kth.se>
%


verify(InputFileName) :-
    see(InputFileName),
    writeln(InputFileName),
    read(Prems),
    read(Goal),
    read(Proof),
    seen,
    valid_proof(Prems, Goal, Proof).