bool CheckCutEquiv(const pool<SigBit>& cut1, SigBit out1,
                   const pool<SigBit>& cut2, SigBit out2)
{
    const pool<SigBit> *six_cut = nullptr;
    const pool<SigBit> *small_cut = nullptr;
    SigBit six_out, small_out;

    if (cut1.size() == 6 && cut2.size() <= 5) {
        six_cut = &cut1;
        small_cut = &cut2;
        six_out = out1;
        small_out = out2;
    } else if (cut2.size() == 6 && cut1.size() <= 5) {
        six_cut = &cut2;
        small_cut = &cut1;
        six_out = out2;
        small_out = out1;
    } else {
        return false;
    }

    std::vector<SigBit> small_inputs;
    pool<SigBit> subset_bits;
    for (auto bit : *small_cut) {
        if (subset_bits.count(bit))
            return false;
        if (!six_cut->count(bit))
            return false;
        subset_bits.insert(bit);
        small_inputs.push_back(bit);
    }

    std::vector<SigBit> six_bits;
    six_bits.reserve(6);
    for (auto bit : *six_cut)
        six_bits.push_back(bit);

    auto eval_mask = [&](const std::vector<SigBit> &inputs, SigBit out, uint64_t &mask) -> bool {
        mask = 0;
        size_t limit = 1ull << inputs.size();
        for (size_t idx = 0; idx < limit; ++idx) {
            dict<SigBit, State> assignment;
            for (size_t b = 0; b < inputs.size(); ++b)
                assignment[inputs[b]] = ((idx >> b) & 1) ? State::S1 : State::S0;

            State val = StateEval(assignment, out);
            if (val == State::Sx)
                return false;
            if (val == State::S1)
                mask |= (1ull << idx);
        }
        return true;
    };

    for (auto drop_bit : six_bits) {
        if (subset_bits.count(drop_bit))
            continue;

        std::vector<SigBit> five_inputs = small_inputs;
        for (auto bit : six_bits) {
            if (subset_bits.count(bit) || bit == drop_bit)
                continue;
            five_inputs.push_back(bit);
        }

        if (five_inputs.size() != 5)
            continue;

        std::vector<SigBit> six_inputs = five_inputs;
        six_inputs.push_back(drop_bit);

        uint64_t mask6 = 0, mask5 = 0;
        if (!eval_mask(six_inputs, six_out, mask6))
            continue;
        if (!eval_mask(five_inputs, small_out, mask5))
            continue;

        uint32_t plane0 = static_cast<uint32_t>(mask6 & 0xFFFFFFFFull);
        uint32_t expected = static_cast<uint32_t>(mask5 & 0xFFFFFFFFull);
        if (plane0 == expected)
            return true;
    }

    return false;
}
