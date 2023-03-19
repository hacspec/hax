/*
* A hacspec library implementation modelled on the nalgebra rust library.
* Functions are modelled and tested against their nalgebra counterparts
* using Quickcheck.

* This ensures, with reasonable probability, that the
* these functions and the nalgebra functions works identically. With this
* assumption, properties about the nalgebra library can be proven in
* hacspec target languages, and allows hacspec implementations to use
* common linear algebra operations.
*
* Each matrix consists of a pair of dimensions and a Seq fx:
* ((2,3), [0,1,2,3,4,5,6])
* represents a 2x3 matrix
*
* Only matrices are supported, vectors can be modelled as dimension (x,1)
* matrices. Note that, unlike the nalgebra library, matrices are
* represented row-by-row instead of column-by-column.
*/

use hacspec_lib::*;

pub type DimType = usize;
pub type Scalar = i128;
pub type Dims = (DimType, DimType);
pub type Matrix = (Dims, Seq<Scalar>);
pub type MatRes = Result<Matrix, u8>;
pub type ScalRes = Result<Scalar, u8>;

// === Errors === //

const DIMENSION_SEQUENCE_LENGTH_MISMATCH: u8 = 10u8;
const INDEX_OUT_OF_BOUNDS: u8 = 11u8;
const SLICE_OUT_OF_BOUNDS: u8 = 12u8;
const DIMENSION_MISMATCH: u8 = 13u8;

// === External Functions === //

/// Generate new matrix using rows, cols and a seq. Returns an error
/// if the product of the given dimensions is larger than the length
/// of the given Seq.

// === External Functions === //

/// Generate new matrix using rows, cols and a seq.
pub fn new(rows: DimType, cols: DimType, seq: Seq<Scalar>) -> MatRes {
    if seq.len() > 0 && rows * cols == seq.len() {
        MatRes::Ok(((rows, cols), seq))
    } else {
        MatRes::Err(DIMENSION_SEQUENCE_LENGTH_MISMATCH)
    }
}

/// Generate a n*m matrix filled with a given scalar.
pub fn repeat(n: DimType, m: DimType, scalar: Scalar) -> Matrix {
    let mut ret = Seq::<Scalar>::new(n * m);

    for i in 0..n * m {
        ret[i] = scalar;
    }

    ((n, m), ret)
}

/// Generate a n*m matrix filled with zeros.
pub fn zeros(n: DimType, m: DimType) -> Matrix {
    repeat(n, m, Scalar::ZERO())
}

/// Generate a n*m matrix filled with ones.
pub fn ones(n: DimType, m: DimType) -> Matrix {
    repeat(n, m, Scalar::ONE())
}

/// Generates an identity matrix. If the matrix is not square,
/// the largest square submatrix (starting at the first row and column)
/// is set to the identity while all other entries are set to zero.
pub fn identity(n: DimType, m: DimType) -> Matrix {
    let mut ret = Seq::<Scalar>::new(n * m);

    for i in 0..min(n, m) {
        let index = i * min(n, m) + i;
        ret[index] = Scalar::ONE();
    }

    ((n, m), ret)
}

/// Gets the index of a matrix. Returns an Error if the given index is out of bounds.
pub fn index(m: Matrix, i: DimType, j: DimType) -> ScalRes {
    let (dim, seq) = m;
    let (rows, cols) = dim;
    let index = i * cols + j;

    if index >= rows * cols {
        ScalRes::Err(INDEX_OUT_OF_BOUNDS)
    } else {
        ScalRes::Ok(seq[index])
    }
}

/// Transposes a matrix.
pub fn transpose(matrix: Matrix) -> Matrix {
    let (dim, seq) = matrix;
    let (rows, cols) = dim;
    let mut ret = Seq::<Scalar>::new(seq.len());

    for i in 0..rows {
        for j in 0..cols {
            let seq_index = i * cols + j;
            let ret_index = j * rows + i;
            ret[ret_index] = seq[seq_index]
        }
    }

    ((cols, rows), ret)
}

/// Returns a matrix slice, given a Matrix and two Dims (pairs of usize),
/// first Dims pair representing the starting point and second Dims
/// pair the dimensions. Returns an Error if the given slice is out of bounds.
pub fn slice(matrix: Matrix, start: Dims, len: Dims) -> MatRes {
    let (dim, seq) = matrix;
    let (rows, cols) = dim;
    let (start_row, start_col) = start;
    let (len_rows, len_cols) = len;
    let start_index = start_row * cols + start_col;
    let mut ret = Seq::<Scalar>::new(len_rows * len_cols);
    let mut res = MatRes::Err(SLICE_OUT_OF_BOUNDS);

    if start_index + len_rows * len_cols <= rows * cols {
        for i in 0..len_rows {
            for j in 0..len_cols {
                let ret_index = i * len_cols + j;
                let seq_index = (start_row + i) * cols + (start_col + j);
                ret[ret_index] = seq[seq_index]
            }
        }

        res = new(len_rows, len_cols, ret);
    }

    res
}

/// Scale a matrix with a given scalar.
pub fn scale(matrix: Matrix, scalar: Scalar) -> Matrix {
    let (dim, seq) = matrix;
    let mut ret = Seq::<Scalar>::new(seq.len());

    for i in 0..seq.len() {
        ret[i] = scalar * seq[i]
    }

    (dim, ret)
}

/// Matrix addition. Returns an Error on dimension mismatch.
pub fn add(matrix_1: Matrix, matrix_2: Matrix) -> MatRes {
    let (m1_dim, m1_s) = matrix_1;
    let (m2_dim, m2_s) = matrix_2;
    let mut ret = Seq::<Scalar>::new(m1_s.len());
    let mut res = MatRes::Err(DIMENSION_MISMATCH);

    if m1_dim == m2_dim {
        for i in 0..m1_s.len() {
            ret[i] = m1_s[i] + m2_s[i]
        }
        res = MatRes::Ok((m1_dim, ret))
    }
    res
}

/// Matrix subtraction. Returns an Error on dimension mismatch.
pub fn sub(matrix_1: Matrix, matrix_2: Matrix) -> MatRes {
    let (m1_dim, m1_s) = matrix_1;
    let (m2_dim, m2_s) = matrix_2;
    let mut ret = Seq::<Scalar>::new(m1_s.len());
    let mut res = MatRes::Err(DIMENSION_MISMATCH);

    if m1_dim == m2_dim {
        for i in 0..m1_s.len() {
            ret[i] = m1_s[i] - m2_s[i]
        }
        res = MatRes::Ok((m1_dim, ret))
    }
    res
}

/// Component-wise multiplication (Hadamard product). Returns an Error on dimension mismatch.
pub fn component_mul(matrix_1: Matrix, matrix_2: Matrix) -> MatRes {
    let (m1_dim, m1_s) = matrix_1;
    let (m2_dim, m2_s) = matrix_2;
    let mut ret = Seq::<Scalar>::new(m1_s.len());
    let mut res = MatRes::Err(DIMENSION_MISMATCH);

    if m1_dim == m2_dim {
        for i in 0..m1_s.len() {
            ret[i] = m1_s[i] * m2_s[i]
        }
        res = MatRes::Ok((m1_dim, ret))
    }
    res
}

/// Matrix multiplication. Returns an Error on dimension mismatch.
pub fn mul(matrix_1: Matrix, matrix_2: Matrix) -> MatRes {
    let (dim_1, seq_1) = matrix_1;
    let (dim_2, seq_2) = matrix_2;
    let (l, m) = dim_1;
    let (m_, n) = dim_2;
    let mut ret = Seq::<Scalar>::new(l * n);
    let mut res = MatRes::Err(DIMENSION_MISMATCH);

    if m == m_ {
        for i in 0..l {
            for j in 0..n {
                let mut acc = Scalar::ZERO();
                let index = i * n + j;

                for k in 0..m {
                    let index_1 = i * m + k;
                    let index_2 = k * n + j;

                    acc = acc + seq_1[index_1] * seq_2[index_2];
                }

                ret[index] = acc
            }
        }

        res = new(l, n, ret)
    }

    res
}
