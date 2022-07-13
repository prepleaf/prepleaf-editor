import React from 'react';
import PropTypes from 'prop-types';
import DraftEditor from './DraftEditor';

class PrepleafEditor extends React.Component {
	render() {
		return <DraftEditor {...this.props} />;
	}
}

PrepleafEditor.propTypes = {
	readOnly: PropTypes.bool.isRequired,
	onChange: PropTypes.func,
};

PrepleafEditor.defaultProps = {
	readOnly: false,
};

export default PrepleafEditor;
