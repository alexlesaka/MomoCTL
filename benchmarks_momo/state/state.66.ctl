A((((~a & b) & c) & ~d) U (((~a & ~b) & ~c) & d))
EF(((~a & ~b) & c) & d)
AF(((~a & b) & c) & ~d)
AF((((a & b) & c) & d) | (((a & ~b) & c) & ~d))
EG(((a & b) & c) & d)
AG((((~a | ~b) | ~c) | ~d) | (EX(((~a & ~b) & c) & d)))
AG((((~a | ~b) | ~c) | ~d) | (EX(((a & ~b) & c) & d)))
AG((((~a | ~b) | ~c) | d) | (EX(((~a & b) & c) & ~d)))
AG((((~a | ~b) | ~c) | d) | (AX(((((~a & b) & c) & ~d) | (((a & ~b) & c) & ~d)) | (((a & b) & ~c) & d))))
AG((((~a | ~b) | c) | ~d) | (EX(((~a & b) & c) & ~d)))
AG((((~a | ~b) | c) | ~d) | (AX((((~a & b) & ~c) & ~d) | (((~a & ~b) & ~c) & ~d))))
AG((((~a | ~b) | c) | d) | (EX(((a & b) & ~c) & ~d)))
AG((((~a | ~b) | c) | d) | (AX(((a & ~b) & ~c) & ~d)))
AG((((~a | ~b) | c) | d) | (AX(((a & ~b) & c) & ~d)))
AG((((~a | ~b) | c) | d) | (AX((((a & b) & c) & ~d) | (((a & b) & ~c) & ~d))))
AG((((~a | ~b) | c) | d) | (AX(((((~a & ~b) & ~c) & d) | (((~a & b) & ~c) & d)) | (((a & ~b) & c) & ~d))))
AG((((~a | b) | ~c) | ~d) | (EX(((a & b) & ~c) & d)))
AG((((~a | b) | ~c) | d) | (EX(((~a & ~b) & ~c) & d)))
AG((((~a | b) | c) | ~d) | (EX(((~a & b) & ~c) & ~d)))
AG((((~a | b) | c) | ~d) | (EX(((a & ~b) & ~c) & d)))
AG((((~a | b) | c) | ~d) | (AX(((((a & b) & ~c) & d) | (((a & ~b) & c) & ~d)) | (((~a & b) & ~c) & ~d))))
AG((((~a | b) | c) | ~d) | (AX(((((a & b) & ~c) & d) | (((a & ~b) & c) & ~d)) | (((a & ~b) & ~c) & ~d))))
AG((((~a | b) | c) | d) | (EX(((~a & ~b) & ~c) & ~d)))
AG((((~a | b) | c) | d) | (EX(((a & b) & ~c) & ~d)))
AG((((a | ~b) | ~c) | ~d) | (EX(((a & b) & c) & d)))
AG((((a | ~b) | ~c) | d) | (EX(((a & b) & c) & ~d)))
AG((((a | ~b) | ~c) | d) | (AX((((a & ~b) & c) & d) | (((~a & ~b) & c) & ~d))))
AG((((a | ~b) | c) | ~d) | (EX(((a & b) & ~c) & d)))
AG((((a | ~b) | c) | ~d) | (EX(((a & b) & c) & d)))
AG((((a | ~b) | c) | d) | (AX(((a & ~b) & c) & d)))
AG((((a | ~b) | c) | d) | (AX(((((a & b) & ~c) & d) | (((a & ~b) & ~c) & d)) | (((~a & b) & c) & ~d))))
AG((((a | b) | ~c) | ~d) | (EX(((~a & ~b) & c) & d)))
AG((((a | b) | ~c) | ~d) | (EX(((~a & b) & ~c) & ~d)))
AG((((a | b) | ~c) | ~d) | (EX(((a & b) & c) & d)))
AG((((a | b) | c) | ~d) | (AX(((~a & b) & c) & ~d)))
