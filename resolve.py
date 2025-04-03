r"""
This is a `SageMath` implementation of the algorithm from Section 3 that relies
on Lemmas 3.4 and 3.5 to verify the claim that no threshold graph $G \in
\mathcal{C}_{n, e}$ such that $G \not\cong \mathcal{D}_{n, e},
\mathcal{V}_{n, e}$ can have the maximum spectral radius on
$\mathcal{C}_{n, e}$, for any $n \ge b_e$, given an input argument $e \ge 4$
such that $t_e \ge 1$.
"""

from pathlib import Path
from typing import List, Optional, Union

from sage.all import *
from sage.rings.polynomial.real_roots import real_roots


# These are the parameters to be used by the `SageMath` real root isolation
# algorithm.
MAX_DIAMETER = 0.1
STRATEGY = None
# STRATEGY = 'warp'


def perform_v_comparison(
    e: Integer,
    outer_poly: Polynomial,
    inner_poly: Polynomial,
    min_order: Integer,
) -> Union[Integer, Rational]:
    r"""
    This auxiliary function inputs a T-subgraph $T$ of size $e$, where
    $e \ge 4$ and $t_e \ge 1$, and performs steps (5) and (6) of the algorithm
    by using Lemma 3.4 to compute the value $n_L$.

    :arg e: The value $e$ that satisfies $e \ge 4$ and $t_e \ge 1$.
    :arg outer_poly: The polynomial $\mathcal{P}_{T \lor K_1}$ divided by the
        GCD of $\mathcal{P}_{T \lor K_1}$ and $\mathcal{P}_{T}$.
    :arg inner_poly: The polynomial $\mathcal{P}_{T}$ divided by the GCD of
        $\mathcal{P}_{T \lor K_1}$ and $\mathcal{P}_{T}$.
    :arg min_order: The value $|T \lor K_1|$, i.e., $|T| + 1$.

    :return: Either a rational number that is a good enough upper bound on the
        value $n_L$, or `None`, if it was not possible to derive this value via
        Lemma 3.4.
    """

    x = ZZ["x"].gen()

    # These two polynomials can be used in place of
    # $\mathcal{P}_{\mathcal{T}(\mathcal{V}_{n, e})}$ and
    # $\mathcal{P}_{\mathcal{T}_1(\mathcal{V}_{n, e})}$, respectively, by
    # virtue of Lemma 3.7.
    inner_poly_v = x**2 - e
    outer_poly_v = (x + 1) * (x**2 - x - 2 * e)

    # Compute the polynomial $\mathcal{Q}_{G, \mathcal{V}_{n, e}} up to a
    # potential nonconstant factor that can be ignored without loss of
    # generality.
    q_poly = (
        x * (outer_poly * inner_poly_v - outer_poly_v * inner_poly)
        + (min_order - e - 2) * inner_poly * inner_poly_v
    )

    # Check that the computed $\mathcal{Q}$-like polynomial has at least one
    # real root and store its largest real root to `root_q`. The variable
    # `root_q` is assigned an ordered pair of rational numbers that represents
    # an interval which contains the largest real root of the
    # $\mathcal{Q}$-like polynomial.
    roots_q = real_roots(q_poly, max_diameter=MAX_DIAMETER, strategy=STRATEGY)
    assert len(roots_q) >= 1
    root_q = roots_q[-1][0]

    # Use the same `SageMath` real root isolation algorithm to find an interval
    # that contains $\rho(\mathcal{T}_1(\mathcal{V}_{n, e}))$. The variable
    # `root_v` is assigned the ordered pair of rational numbers that represents
    # this interval.
    roots_v = real_roots(outer_poly_v, max_diameter=MAX_DIAMETER)
    root_v = roots_v[-1][0]

    # Apply Lemma 3.4(i) if possible.
    if root_q[1] < root_v[0]:
        return e + 2

    # Otherwise, apply Lemma 3.4(ii) if possible.
    if root_q[0] > root_v[1]:
        # Use the rational upper bound instead of the root itself, so that a
        # rational upper bound is obtained for $n_L$.
        val = root_q[1]
        threshold = e + 2 + val * outer_poly_v(val) / inner_poly_v(val)

        return threshold

    # If the intervals which contain the real roots are such that neither
    # Lemma 3.4(i) nor Lemma 3.4(ii) can be applied, report failure and return
    # `None`.
    return None


def perform_d_comparison(
    k: Integer,
    t: Integer,
    outer_poly: Polynomial,
    inner_poly: Polynomial,
    min_order: Integer,
) -> Optional[Union[Integer, Rational]]:
    r"""
    This auxiliary function inputs a T-subgraph $T$ of size $e$, where
    $e \ge 4$ and $t_e \ge 1$, and performs steps (2), (3) and (4) of the
    algorithm by using Lemma 3.5 to report success or compute the value $n_U$.

    :arg k: The number $k_e \ge 3$ for the value $e$.
    :arg t: The number $t_e \ge 1$ for the value $e$.
    :arg outer_poly: The polynomial $\mathcal{P}_{T \lor K_1}$ divided by the
        GCD of $\mathcal{P}_{T \lor K_1}$ and $\mathcal{P}_{T}$.
    :arg inner_poly: The polynomial $\mathcal{P}_{T}$ divided by the GCD of
        $\mathcal{P}_{T \lor K_1}$ and $\mathcal{P}_{T}$.
    :arg min_order: The value $|T \lor K_1|$, i.e., $|T| + 1$.

    :return: Either -1, if Lemma 3.5(i) was applied, or a positive rational
        number that is a good enough lower bound on the value $n_U$, if
        Lemma 3.5(ii) was applied, or `None`, if it was not possible to apply
        Lemma 3.5 at all.
    """

    x = ZZ["x"].gen()

    # These two polynomials can be used in place of
    # $\mathcal{P}_{\mathcal{T}(\mathcal{D}_{n, e})}$ and
    # $\mathcal{P}_{\mathcal{T}_1(\mathcal{D}_{n, e})}$, respectively, by
    # virtue of Lemma 3.6.
    inner_poly_d = x**3 - (k - 2) * x**2 - (k + t - 1) * x + t * (k - t - 1)
    outer_poly_d = (x + 1) * (
        x**3 - (k - 1) * x**2 - (k + t + 1) * x + (t + 1) * (k - t - 1)
    )

    # Compute the polynomial $\mathcal{Q}_{G, \mathcal{D}_{n, e}} up to a
    # potential nonconstant factor that can be ignored without loss of
    # generality.
    q_poly = (
        x * (outer_poly * inner_poly_d - outer_poly_d * inner_poly)
        + (min_order - k - 2) * inner_poly * inner_poly_d
    )

    # Use the `SageMath` real root isolation algorithm to find an interval that
    # contains $\rho(\mathcal{T}_1(\mathcal{D}_{n, e}))$. The variable `root_d`
    # is assigned the ordered pair of rational numbers that represents this
    # interval.
    roots_d = real_roots(outer_poly_d, max_diameter=MAX_DIAMETER)
    root_d = roots_d[-1][0]

    # If the $\mathcal{Q}$-like polynomial has a positive lead coefficient,
    # try to apply Lemma 3.5(i).
    if q_poly.leading_coefficient() >= 1:
        # If the $\mathcal{Q}$-like polynomial has no real root, then there is
        # nothing more to discuss and the value -1 can be returned in
        # accordance with step (3) of the algorithm. Otherwise, use the
        # variable `root_q` to store an ordered pair of rational numbers that
        # represents an interval which contains the largest real root of the
        # $\mathcal{Q}$-like polynomial.
        roots_q = real_roots(
            q_poly, max_diameter=MAX_DIAMETER, strategy=STRATEGY
        )
        if len(roots_q) < 1:
            return -1

        root_q = roots_q[-1][0]

        # If we can guarantee that the largest real root of the
        # $\mathcal{Q}$-like polynomial is below
        # $\rho(\mathcal{T}_1(\mathcal{D}_{n, e}))$, then the value -1 can be
        # returned by Lemma 3.5(i).
        if root_q[1] < root_d[0]:
            return -1

        # Otherwise, report failure and return `None`.
        return None

    # If the $\mathcal{Q}$-like polynomial has a negative lead coefficient,
    # try to apply Lemma 3.5(ii).
    if q_poly.leading_coefficient() <= -1:
        # Check that the computed $\mathcal{Q}$-like polynomial has at least
        # one real root and that its largest real root is simple. Also use the
        # variable `root_q` to store an ordered pair of rational numbers that
        # represents an interval which contains the largest real root of the
        # $\mathcal{Q}$-like polynomial.
        roots_q = real_roots(
            q_poly, max_diameter=MAX_DIAMETER, strategy=STRATEGY
        )
        assert len(roots_q) >= 1
        assert roots_q[-1][1] == 1
        root_q = roots_q[-1][0]

        # If the $\mathcal{Q}$-like polynomial has another real root distinct
        # from its largest real root, then this root must be guaranteed to be
        # below $\rho(\mathcal{T}_1(\mathcal{D}_{n, e}))$. If such a guarantee
        # cannot be made, report failure and return `None`.
        if len(roots_q) >= 2:
            root_q_2 = roots_q[-2][0]
            if not root_d[0] > root_q_2[1]:
                return None

        # The largest real root of the $\mathcal{Q}$-like polynomial must be
        # guaranteed to be above $\rho(\mathcal{T}_1(\mathcal{D}_{n, e}))$. If
        # such a guarantee cannot be made, report failure and return `None`.
        if not root_d[1] < root_q[0]:
            return None

        # Apply Lemma 3.5(ii) and use the rational lower bound instead of the
        # root itself, so that a rational lower bound is obtained for $n_U$.
        val = root_q[0]
        threshold = k + 2 + val * outer_poly_d(val) / inner_poly_d(val)

        return threshold

    # If the $\mathcal{Q}$-like polynomial is a zero polynomial, report failure
    # and return `None`.
    return None


def resolve_t_subgraph(t_subgraph: List[Integer]) -> bool:
    r"""
    This is the main function that performs the verification process for a
    given T-subgraph $T$ and outputs whether the verification was successful.
    If the verification is successful, this means that any threshold graph from
    $\mathcal{C}_{n, e}$ with the T-subgraph $T$ has a spectral radius
    strictly below $\rho(\mathcal{D}_{n, e})$ or $\rho(\mathcal{V}_{n, e})$. If
    the verification is not successful, then this does not necessarily imply
    anything. Since the `SageMath` real root isolation algorithm is not
    deterministic, neither is this function. In order to discard connected
    threshold graphs with the T-subgraph $T$ as potential solutions to the
    spectral radius maximization problem on $\mathcal{C}_{n, e}$, it suffices
    to obtain the output `True` via this function in at least one execution.

    :arg t_subgraph: A strictly decreasing list of positive integers that
        represents the T-subgraph of interest $T$. The length of the list is
        the maximal $c$ such that $A_{c, c + 1} = 1$, where $A$ is the stepwise
        adjacency matrix of $T$. For each $i = 1, 2, \ldots, c$, the element
        `t_subgraph[i]` is the maximal $s$ such that $A_{i, i + s} = 1$.

    :return: A boolean that determines whether the verification process was
        successful.
    """

    # The parameter $e$ is computed and it is checked whether $e \ge 4$, as
    # required.
    e = sum(t_subgraph)
    assert e >= 4

    # The value $k_e$ is computed.
    k = 1
    while k * (k - 1) // 2 + (k - 1) < e:
        k += 1

    # The value $t_e$ is computed.
    t = e - k * (k - 1) // 2
    # If $t_e = 0$, then there is nothing more to do since this case was
    # already settled by Bell.
    if t == 0:
        return True

    # Ignore the T-subgraph that corresponds to $\mathcal{V}_{n, e}$.
    if len(t_subgraph) < 2:
        return True

    # Find the T-subgraph that corresponds to $\mathcal{D}_{n, e}$.
    d_t_subgraph = list(range(k - 1, 0, -1))
    for index in range(t):
        d_t_subgraph[index] += 1

    # If the given T-subgraph $T$ is precisely the one that corresponds to
    # $\mathcal{D}_{n, e}$, then ignore it.
    if len(t_subgraph) == len(d_t_subgraph):
        good = False
        for item_1, item_2 in zip(t_subgraph, d_t_subgraph):
            if item_1 != item_2:
                good = True
                break

        if not good:
            return True

    # Compute the value $|T|$ and store it to `alpha`.
    alpha = max(t_subgraph) + 1

    # Create the adjacency matrix of $T$.
    inner_mat = matrix(alpha)
    for index, item in enumerate(t_subgraph):
        inner_mat[index, index + 1 : index + item + 1] = 1
        inner_mat[index + 1 : index + item + 1, index] = 1

    # Create the adjacency matrix of $T \lor K_1$.
    outer_mat = matrix(alpha + 1)
    outer_mat[1:, 1:] = inner_mat
    outer_mat[0, 1:] = 1
    outer_mat[1:, 0] = 1

    # Find the characteristic polynomials of $T$ and $T \lor K_1$,
    # respectively.
    inner_poly = inner_mat.charpoly()
    outer_poly = outer_mat.charpoly()

    # Divide the two obtained polynomials by their GCD so that the two new
    # polynomials are coprime. The two new polynomials can now be used in place
    # of $\mathcal{P}_T$ and $\mathcal{P}_{T \lor K_1}$ without loss of
    # generality.
    aux_poly = gcd(inner_poly, outer_poly)
    inner_poly = inner_poly // aux_poly
    outer_poly = outer_poly // aux_poly

    # Perform steps (2), (3) and (4) of the algorithm.
    threshold_d = perform_d_comparison(
        k, t, outer_poly, inner_poly, alpha + 1
    )
    # If an error occurred, then report failure and stop the verification.
    if threshold_d is None:
        return False
    # If Lemma 3.5(i) applied, then report success and stop the verification
    # in accordance with step (3).
    if threshold_d == -1:
        return True

    # Otherwise, perform steps (5) and (6) of the algorithm.
    threshold_v = perform_v_comparison(e, outer_poly, inner_poly, alpha + 1)
    # If an error occurred, then report failure and stop the verification.
    if threshold_v is None:
        return False

    # If the obtained lower bound on $n_U$ is greater than the obtained upper
    # on $n_L$, this means that $n_U > n_L$, hence the algorithm successfully
    # ends in accordance with step (7). Otherwise, report failure.
    return threshold_d - threshold_v > 5


def resolve_file(input_file: Path, output_folder: Path) -> None:
    r"""
    This function traverses a given input file containing T-subgraphs in
    separate lines and performs the verification process on each T-subgraph via
    the `resolve_t_subgraph` function. If the verification process is
    successful for each T-subgraph, then an empty file with the same stem and
    the extension `.success` is created in the output folder whose path is also
    specified. If the verification process fails for at least one T-subgraph,
    then a file with the same stem and the extension `.failure` is created in
    the output folder. In the latter case, each T-subgraph for which the
    verification fails is stored in the output file in a separate line. All
    T-subgraphs are represented as a strictly decreasing list of positive
    integers in the manner described in the function `resolve_t_subgraph`.

    :arg input_file: The path of the input file, given as a `Path` object.
    :arg output_folder: The path of the output folder, given as a `Path`
        object.
    """

    # This list is meant to store the T-subgraphs for which the verification
    # process fails.
    problems = []

    with open(str(input_file), "r") as opened_file:
        # Iterate over all the lines of the input file.
        for line in opened_file:
            # Read the line and parse it into a T-subgraph.
            t_subgraph = line.strip().split()
            t_subgraph = list(map(int, t_subgraph))

            # If the verification process fails, save the T-subgraph to the
            # list `problems`.
            if not resolve_t_subgraph(t_subgraph):
                problems.append(t_subgraph)

    # If the verification process was successful for all the T-subgraphs,
    # create the empty `.success` file.
    if len(problems) == 0:
        output_file = output_folder / f"{input_file.stem}.success"
        with open(str(output_file), "w") as opened_file:
            pass

    # Otherwise, create the `.failure` file and use it to store the T-subgraphs
    # for which the verification process was not successful.
    else:
        output_file = output_folder / f"{input_file.stem}.failure"
        with open(str(output_file), "w") as opened_file:
            for problem in problems:
                opened_file.write(f"{problem}\n")
