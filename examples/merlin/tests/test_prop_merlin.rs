extern crate quickcheck;

use hacspec_lib::*;
use hacspec_merlin::*;

use quickcheck::*;

// === Helper functions === //

fn quickcheck(helper: impl Testable) {
	QuickCheck::new()
		.tests(100)
		.min_tests_passed(100)
		.max_tests(1000000)
		.quickcheck(helper);
} 

// Converts a string to a byte
fn b(s: &str) -> Seq<U8> {
	let xs = Seq::<u8>::from_vec(s.to_string().into_bytes());

	let mut ret = Seq::<U8>::new(xs.len());
	for i in 0..xs.len() {
		ret[i] = U8::classify(xs[i])
	}
	ret
}

// Converts a ByteVec to a Secret ByteSeq
fn to_seq(xs: Vec<u8>) -> Seq<U8> {
	let mut ret = Seq::<U8>::new(xs.len());
	for i in 0..xs.len() {
		ret[i] = U8::classify(xs[i])
	}
	ret
}

// === Tests === //

// Tests all merlin functions against the external merlin counterparts.
#[test]
fn merl_test_all_funcs() {
	fn helper(msg: Vec<u8>, n: u64, buf_size: u8) -> TestResult {
		let mut ret = true;
		let mut t1 = new(b("str"));
		let mut t2 = merlin::Transcript::new(b"str");
		let mut buf = Vec::<u8>::new();
		buf.resize(buf_size as usize, 0);

		t1 = append_message(t1, b("msg"), to_seq(msg.clone()));
		t1 = append_U64(t1, b("n"), U64::classify(n));

		t2.append_message(b"msg", &msg);
		t2.append_u64(b"n", n);

		let (_, data) = challenge_bytes(t1, b("challenge_label"), to_seq(buf.clone()));
		t2.challenge_bytes(b"challenge_label", &mut buf);

		if data.len() != buf.len() {
			ret = false
		}
		for i in 0..data.len() {
			if data[i].declassify() != buf[i] {
				ret = false;
			}
		}

		TestResult::from_bool(ret)
	}
	quickcheck(helper as fn(Vec<u8>, u64, u8) -> TestResult);
}
