//! `nocompiler prove`'s report (crate::prove): the check, the generator's selection and its
//! rows joined into one outcome per function.

use nocompiler::prove::{Outcome, json, markdown, rows};

#[test]
fn each_function_gets_one_outcome_with_its_reason() {
    let check = vec![
        ("memset".to_string(), 30, "L2".to_string()),
        ("fwrite".to_string(), 40, "L2".to_string()),
        (
            "__lock".to_string(),
            12,
            "below L0 (R1 decode 0x...)".to_string(),
        ),
        ("loopy".to_string(), 20, "L2".to_string()),
        ("odd.name".to_string(), 5, "L2".to_string()),
    ];
    let selection = "memset\t30\tattempted\nfwrite\t40\tattempted\n__lock\t12\tnot attempted: no _dom (a callee failed the profile check)\nloopy\t20\tnot attempted: loops nested, or a loop with more than one back edge to its head\n";
    // memset: failed at safe, proved at anyread; fwrite: failed at both.
    let results = "memset\t30\tsafe\t1\terror: unsolved goals\nmemset\t30\tanyread\t0\t\nfwrite\t40\tsafe\t1\t/x.lean:3:0: error: timeout\nfwrite\t40\tanyread\t124\t\n";
    let proved = "memset\tanyread\tQ3_anyread.lean\tArt.Q3.safe\n";
    let r = rows(&check, selection, results, proved);
    assert_eq!(
        r[0].outcome,
        Outcome::Proved {
            spec: "anyread".into()
        }
    );
    assert_eq!(
        r[1].outcome,
        Outcome::Failed {
            reason: "timeout (300 s)".into()
        }
    );
    assert!(
        matches!(&r[2].outcome, Outcome::NotAttempted { reason } if reason.starts_with("no _dom"))
    );
    assert!(
        matches!(&r[3].outcome, Outcome::NotAttempted { reason } if reason.starts_with("loops nested"))
    );
    assert_eq!(
        r[4].outcome,
        Outcome::NotAttempted {
            reason: "not exported".into()
        }
    );
    let md = markdown("x.elf", &r);
    assert!(
        md.contains("1 of 5 functions proved automatically (30 of 107 instructions)."),
        "{md}"
    );
    assert!(md.contains("| proved (anyread) | 1 | `memset` |"), "{md}");
    assert!(
        md.contains("proved (anyread): `Art.Q3.safe` in Q3_anyread.lean"),
        "{md}"
    );
    assert_eq!(r[1].theorem, None);
    let j = json(&r);
    assert!(j.contains("\"name\":\"memset\",\"instructions\":30,\"level\":\"L2\",\"outcome\":\"proved\",\"detail\":\"anyread\",\"theorem\":{\"module\":\"Q3_anyread.lean\",\"name\":\"Art.Q3.safe\"}"), "{j}");
}
