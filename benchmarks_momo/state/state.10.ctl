E((((~a & b) & c) & ~d) U (((a & ~b) & ~c) & d))
E((((a & ~b) & ~c) & d) U (((~a & b) & ~c) & d))
E((((a & b) & ~c) & ~d) U (((~a & b) & c) & d))
A((((a & b) & ~c) & d) U (((~a & ~b) & ~c) & d))
AG((((~a | ~b) | ~c) | ~d) | (AX(((((~a & ~b) & c) & d) | (((a & ~b) & ~c) & d)) | (((a & ~b) & ~c) & ~d))))
AG((((~a | ~b) | ~c) | d) | (AX((((~a & ~b) & c) & d) | (((~a & b) & ~c) & ~d))))
AG((((~a | ~b) | c) | ~d) | (EX(((~a & ~b) & ~c) & d)))
AG((((~a | ~b) | c) | ~d) | (EX(((~a & b) & ~c) & d)))
AG((((~a | ~b) | c) | ~d) | (EX(((a & ~b) & c) & ~d)))
AG((((~a | ~b) | c) | ~d) | (AX(((a & b) & ~c) & ~d)))
AG((((~a | ~b) | c) | ~d) | (AX(((((~a & b) & c) & ~d) | (((~a & b) & ~c) & d)) | (((~a & b) & c) & d))))
AG((((~a | ~b) | c) | ~d) | (AX(((((a & ~b) & c) & d) | (((a & ~b) & ~c) & ~d)) | (((a & b) & ~c) & ~d))))
AG((((~a | ~b) | c) | d) | (EX(((~a & b) & ~c) & ~d)))
AG((((~a | b) | ~c) | ~d) | (EX(((~a & ~b) & c) & ~d)))
AG((((~a | b) | ~c) | d) | (EX(((a & b) & c) & ~d)))
AG((((~a | b) | ~c) | d) | (AX(((a & b) & c) & ~d)))
AG((((~a | b) | c) | ~d) | (AX(((~a & ~b) & c) & ~d)))
AG((((~a | b) | c) | d) | (EX(((~a & b) & c) & d)))
AG((((~a | b) | c) | d) | (AX(((((~a & ~b) & ~c) & ~d) | (((a & b) & ~c) & ~d)) | (((~a & b) & ~c) & d))))
AG((((a | ~b) | ~c) | ~d) | (EX(((a & b) & c) & ~d)))
AG((((a | ~b) | ~c) | ~d) | (AX(((a & ~b) & c) & d)))
AG((((a | ~b) | ~c) | ~d) | (AX((((a & b) & ~c) & d) | (((~a & b) & ~c) & ~d))))
AG((((a | ~b) | ~c) | d) | (EX(((~a & ~b) & ~c) & ~d)))
AG((((a | ~b) | c) | ~d) | (EX(((a & ~b) & c) & d)))
AG((((a | ~b) | c) | ~d) | (AX(((~a & ~b) & c) & d)))
AG((((a | ~b) | c) | d) | (EX(((~a & ~b) & c) & ~d)))
AG((((a | ~b) | c) | d) | (EX(((a & ~b) & c) & d)))
AG((((a | b) | ~c) | ~d) | (EX(((a & ~b) & c) & ~d)))
AG((((a | b) | ~c) | d) | (AX(((~a & ~b) & c) & ~d)))
AG((((a | b) | ~c) | d) | (AX(((((a & ~b) & c) & d) | (((a & b) & c) & ~d)) | (((a & ~b) & c) & d))))
AG((((a | b) | c) | ~d) | (AX(((a & ~b) & ~c) & ~d)))
AG((((a | b) | c) | d) | (EX(((a & ~b) & c) & d)))
AG((((a | b) | c) | d) | (AX(((a & ~b) & ~c) & ~d)))
AG((((a | b) | c) | d) | (AX(((a & ~b) & c) & d)))
EX((((~a & b) & c) & ~d) | (((a & ~b) & c) & d))
