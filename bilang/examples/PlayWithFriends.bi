join A(secret: int);
join B(secret) where B.secret == A.secret;
[play]
withdraw ...