AF((((a & b) & ~c) & ~d) | (((a & ~b) & c) & ~d))
AG((((~a | ~b) | ~c) | ~d) | (EX(((a & b) & ~c) & ~d)))
AG((((~a | ~b) | c) | ~d) | (EX(((~a & ~b) & c) & ~d)))
AG((((~a | ~b) | c) | ~d) | (EX(((a & b) & ~c) & ~d)))
AG((((~a | ~b) | c) | ~d) | (EX(((a & b) & ~c) & d)))
AG((((~a | ~b) | c) | d) | (EX(((~a & b) & c) & d)))
AG((((~a | ~b) | c) | d) | (AX(((~a & b) & c) & ~d)))
AG((((~a | ~b) | c) | d) | (AX(((a & ~b) & ~c) & ~d)))
AG((((~a | b) | ~c) | ~d) | (EX(((~a & ~b) & c) & ~d)))
AG((((~a | b) | ~c) | ~d) | (AX((((a & ~b) & c) & d) | (((a & b) & ~c) & d))))
AG((((~a | b) | ~c) | d) | (EX(((a & b) & ~c) & d)))
AG((((~a | b) | c) | ~d) | (AX(((((a & ~b) & ~c) & d) | (((~a & b) & c) & d)) | (((a & b) & ~c) & d))))
AG((((~a | b) | c) | d) | (EX(((a & b) & ~c) & d)))
AG((((a | ~b) | ~c) | ~d) | (AX(((~a & b) & ~c) & ~d)))
AG((((a | ~b) | ~c) | ~d) | (AX((((a & b) & c) & d) | (((~a & b) & c) & ~d))))
AG((((a | ~b) | ~c) | d) | (EX(((a & b) & ~c) & d)))
AG((((a | ~b) | ~c) | d) | (AX((((a & ~b) & ~c) & ~d) | (((~a & ~b) & c) & ~d))))
AG((((a | ~b) | ~c) | d) | (AX(((((~a & ~b) & ~c) & d) | (((a & ~b) & ~c) & ~d)) | (((~a & ~b) & c) & ~d))))
AG((((a | ~b) | c) | ~d) | (EX(((~a & ~b) & ~c) & d)))
AG((((a | ~b) | c) | ~d) | (EX(((a & b) & c) & d)))
AG((((a | ~b) | c) | ~d) | (AX(((~a & ~b) & ~c) & d)))
AG((((a | ~b) | c) | ~d) | (AX(((~a & b) & ~c) & d)))
AG((((a | ~b) | c) | ~d) | (AX(((((a & b) & ~c) & ~d) | (((~a & ~b) & c) & ~d)) | (((~a & ~b) & ~c) & ~d))))
AG((((a | ~b) | c) | d) | (EX(((~a & ~b) & c) & d)))
AG((((a | b) | ~c) | ~d) | (EX(((a & ~b) & ~c) & ~d)))
AG((((a | b) | ~c) | ~d) | (EX(((a & ~b) & ~c) & d)))
AG((((a | b) | ~c) | ~d) | (EX(((a & b) & c) & d)))
AG((((a | b) | ~c) | d) | (AX(((((~a & b) & c) & d) | (((a & b) & ~c) & ~d)) | (((a & b) & c) & ~d))))
AG((((a | b) | c) | ~d) | (EX(((a & ~b) & ~c) & d)))
AG((((a | b) | c) | d) | (EX(((~a & b) & ~c) & ~d)))
AG((((a | b) | c) | d) | (AX(((((a & b) & ~c) & ~d) | (((~a & b) & ~c) & ~d)) | (((a & b) & c) & d))))
AG~d
AG~b
AG~a
AGc
AX(((~a & ~b) & ~c) & d)
AX(((a & b) & ~c) & d)